use crate::Span;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

/// Represents the source location (row, column) of this element in the original Ion text.
///
/// The source location metadata is primarily intended for error reporting and debugging purposes,
/// helping applications provide meaningful feedback to users about the source of issues.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Default)]
pub struct SourceLocation {
    /// A 1-based row and column pair.
    /// INVARIANT: both components must be `0` or both must be non-zero.
    location: (usize, usize),
}

impl SourceLocation {
    /// Constructs a new SourceLocation. If either of `row` or `column` is `0`, returns an instance
    /// with no row/column value (i.e. both row and column are zero). This maintains the invariant
    /// that the location field must be `(0, 0)` or must have two non-zero values.
    pub(crate) fn new(row: usize, column: usize) -> SourceLocation {
        if row == 0 || column == 0 {
            return Self::empty();
        }
        Self {
            location: (row, column),
        }
    }

    /// Constructs a new `SourceLocation` instance that has no row/column available.
    pub(crate) fn empty() -> SourceLocation {
        Self { location: (0, 0) }
    }

    /// If this `SourceLocation` instance has row-column information, returns a tuple containing
    /// the 1-based row and column numbers. Otherwise, returns [`None`].
    pub fn row_column(&self) -> Option<(usize, usize)> {
        match self.location {
            (0, 0) => None,
            other => Some(other),
        }
    }

    /// If this `SourceLocation` instance has row-column information, returns the 1-based row number.
    /// Otherwise, returns [`None`].
    pub fn row(&self) -> Option<usize> {
        match self.location {
            (0, 0) => None,
            (row, _) => Some(row),
        }
    }

    /// If this `SourceLocation` instance has row-column information, returns the 1-based column number.
    /// Otherwise, returns [`None`].
    pub fn column(&self) -> Option<usize> {
        match self.location {
            (0, 0) => None,
            (_, col) => Some(col),
        }
    }
}

#[cfg(test)]
mod source_location_tests {
    use crate::location::SourceLocation;
    #[test]
    fn empty_source_location() {
        let location = SourceLocation::empty();
        assert_eq!(None, location.row_column());
        assert_eq!(None, location.row());
        assert_eq!(None, location.column());
    }

    #[test]
    fn non_empty_source_location() {
        let location = SourceLocation::new(2, 3);
        assert_eq!(Some((2, 3)), location.row_column());
        assert_eq!(Some(2), location.row());
        assert_eq!(Some(3), location.column());
    }
}

/// Encapsulates location tracking state and functionality.
///
/// This struct is cheap to clone because all of its state is behind a single reference-counted
/// pointer, which is shared with every clone.
#[derive(Debug, Clone)]
pub(crate) struct SourceLocationState {
    state: Rc<SourceLocationStateInner>,
}

/// The state shared by a [`SourceLocationState`] and all of its clones.
///
/// Both fields live behind the same `Rc` so that it is impossible to construct or replace one
/// without the other; see the invariants on `last_row`.
#[derive(Debug)]
struct SourceLocationStateInner {
    /// A non-empty vec containing the offset of the start of each row.
    ///
    /// INVARIANTS:
    /// * The first row always starts at offset 0.
    /// * The offsets are sorted in ascending order. [`SourceLocationState::calculate_location_for_span`]
    ///   binary searches this vec, which is meaningful only if it is sorted, and subtracts the
    ///   located row's offset from the span's start, which would underflow if it were not.
    /// * The vec is append-only: rows are never removed, reordered, or rewritten, so a row index
    ///   that was once in bounds remains in bounds.
    row_start_offsets: RefCell<Vec<usize>>,
    /// The 0-based index into `row_start_offsets` that was resolved by the most recent call to
    /// [`SourceLocationState::calculate_location_for_span`] -- made through this
    /// `SourceLocationState` or any of its clones, as the cache is shared with all of them. (The
    /// [`SourceLocation`] that call returns is 1-based; this is the raw vec index.) It is
    /// used as the starting point for the next lookup, which then only has to walk forward.
    ///
    /// Lookups that arrive in ascending order of span offset are O(1) amortized, because the cursor
    /// advances at most once per row per ascending run. `impl TryFrom<LazyValue> for Element`
    /// guarantees that order for literal-backed values by resolving a container's location before
    /// reading -- and thereby recursively materializing -- its children. Lookups that arrive out of
    /// order still get correct results, but pay for a binary search; Ion 1.1 template argument
    /// reordering is a known non-ascending case, because `ExpandedValueSource::via_variable`
    /// preserves the original argument's span, so a template body that references its parameters
    /// out of positional order yields descending spans. (This is a separate property from the
    /// monotonically non-decreasing `stream_offset` that
    /// [`SourceLocationState::update_from_source`] requires: that one is an invariant, this one is
    /// only an optimization.)
    ///
    /// INVARIANT: this is always a valid index into `row_start_offsets`, because that vec is
    /// append-only and the two fields are always constructed and replaced together.
    ///
    /// The value is purely an optimization: any value satisfying the invariant above still yields
    /// a correct result, because the cached row is re-validated against each span before it is
    /// used.
    last_row: Cell<usize>,
    /// The number of lookups that could not start from `last_row` and had to binary search
    /// `row_start_offsets` instead.
    ///
    /// Because the cursor is only an optimization, nothing observable depends on this count; it
    /// exists so that tests can assert the ascending-order property described on `last_row`, which
    /// no other assertion can detect. It is `#[cfg(test)]` so that production builds do not pay
    /// for it.
    #[cfg(test)]
    fallback_lookups: Cell<usize>,
}

impl SourceLocationState {
    pub fn new() -> Self {
        Self {
            state: Rc::new(SourceLocationStateInner {
                row_start_offsets: RefCell::new(vec![0]),
                last_row: Cell::new(0),
                #[cfg(test)]
                fallback_lookups: Cell::new(0),
            }),
        }
    }

    /// The number of lookups made through this `SourceLocationState` or any of its clones that had
    /// to fall back to a binary search. See `SourceLocationStateInner::fallback_lookups`.
    #[cfg(test)]
    pub(crate) fn fallback_lookups(&self) -> usize {
        self.state.fallback_lookups.get()
    }

    /// Updates the location tracking state from the given source data.
    ///
    /// `stream_offset` is the offset of `data` within the stream as a whole. Callers must supply
    /// successive pieces of the stream with monotonically non-decreasing `stream_offset` values;
    /// otherwise the ascending-order invariant of `row_start_offsets` would be violated.
    pub fn update_from_source<T: AsRef<[u8]>>(&mut self, stream_offset: usize, data: T) {
        let data = data.as_ref();
        if !data.is_empty() {
            let newlines = memchr::memchr_iter(b'\n', data);
            self.state
                .row_start_offsets
                .borrow_mut()
                .extend(newlines.map(|it| it + stream_offset + 1));
        }
    }

    pub fn calculate_location_for_span(&self, span: Span<'_>) -> SourceLocation {
        let range = span.range();
        let row_start_offsets = self.state.row_start_offsets.borrow();

        // `row_start_offsets` is sorted, so the row containing `range.start` is the last one whose
        // offset does not exceed it. `impl TryFrom<LazyValue> for Element` requests locations in
        // ascending order for literal-backed values, so the cached row is normally the answer or is
        // a short walk behind it. (Ion 1.1 template argument reordering is a known exception; see
        // the docs on `last_row`.)
        let last_row = self.state.last_row.get();
        let row = if row_start_offsets
            .get(last_row)
            .is_some_and(|&start| start <= range.start)
        {
            // Advance while the following row also starts at or before `range.start`. Within an
            // ascending run of lookups the cursor only moves forward, so it advances at most `rows`
            // times over the whole run -- O(1) amortized per lookup, and a single comparison when
            // consecutive spans share a row. (The `else` branch below can reset the cursor
            // backwards, which starts a new run; a forward walk after such a reset is O(rows).)
            // For a fixed-slice input, where the whole row index is built up front, searching
            // from scratch on every lookup would instead cost O(log rows) at best and O(rows) for
            // a linear scan, making a complete read O(rows * spans).
            let mut row = last_row;
            while row_start_offsets
                .get(row + 1)
                .is_some_and(|&next| next <= range.start)
            {
                row += 1;
            }
            row
        } else {
            // `range.start` precedes the cached row, so the caller is not querying in ascending
            // order. Still correct, just without the amortized bound.
            //
            // `partition_point` counts the offsets at or before `range.start`; the row index is one
            // less. The count is always at least 1 because of the invariant that the first row
            // starts at offset 0.
            #[cfg(test)]
            self.state
                .fallback_lookups
                .set(self.state.fallback_lookups.get() + 1);
            row_start_offsets.partition_point(|&offset| offset <= range.start) - 1
        };

        self.state.last_row.set(row);
        let row_start_offset = row_start_offsets[row];
        debug_assert!(
            row_start_offset <= range.start,
            "row {row} starts at offset {row_start_offset}, which is after the span's start ({})",
            range.start
        );
        let column = range.start - row_start_offset;
        // Both of these are 0-based counts, and must be incremented to be 1-based row/column
        SourceLocation::new(row + 1, column + 1)
    }
}

#[cfg(test)]
mod source_location_state_tests {
    use crate::location::SourceLocationState;
    use crate::Span;
    use rstest::rstest;

    /// `"a\nbb\n\nccc"` -- rows start at offsets 0, 2, 5, and 6.
    fn state() -> SourceLocationState {
        let mut state = SourceLocationState::new();
        state.update_from_source(0, b"a\nbb\n\nccc");
        state
    }

    fn location_at(state: &SourceLocationState, offset: usize) -> Option<(usize, usize)> {
        state
            .calculate_location_for_span(Span::with_offset(offset, b""))
            .row_column()
    }

    #[rstest]
    #[case::first_row_start(0, (1, 1))]
    #[case::first_row_terminator(1, (1, 2))]
    #[case::second_row_start(2, (2, 1))]
    #[case::second_row_interior(3, (2, 2))]
    #[case::second_row_terminator(4, (2, 3))]
    #[case::empty_row(5, (3, 1))]
    #[case::last_row_start(6, (4, 1))]
    #[case::last_row_interior(8, (4, 3))]
    fn location_for_offset(#[case] offset: usize, #[case] expected: (usize, usize)) {
        assert_eq!(Some(expected), location_at(&state(), offset));
    }

    /// Lookups are cached across calls, so a sequence of them must produce the same locations as
    /// the same lookups made in isolation, regardless of the order they arrive in. Readers query
    /// offsets in increasing order, but nothing in the API requires it. Each case is a sequence of
    /// `(offset, expected location)` pairs applied to a single state instance; each pair is also
    /// checked against a state whose cache is cold.
    #[rstest]
    #[case::ascending([(0, (1, 1)), (1, (1, 2)), (2, (2, 1)), (3, (2, 2)), (4, (2, 3)), (5, (3, 1)), (6, (4, 1)), (8, (4, 3))])]
    #[case::descending([(8, (4, 3)), (6, (4, 1)), (5, (3, 1)), (4, (2, 3)), (3, (2, 2)), (2, (2, 1)), (1, (1, 2)), (0, (1, 1))])]
    #[case::repeated_same_row([(6, (4, 1)), (8, (4, 3)), (6, (4, 1)), (8, (4, 3)), (6, (4, 1))])]
    #[case::alternating_distant_rows([(0, (1, 1)), (8, (4, 3)), (1, (1, 2)), (6, (4, 1)), (2, (2, 1)), (5, (3, 1))])]
    // Each lookup below must reject the cached row and resolve an earlier one.
    #[case::backward_cache_misses([(8, (4, 3)), (2, (2, 1)), (0, (1, 1))])]
    fn lookups_are_order_independent<const N: usize>(
        #[case] lookups: [(usize, (usize, usize)); N],
    ) {
        let warm_state = state();
        for (offset, expected) in lookups {
            assert_eq!(
                Some(expected),
                location_at(&warm_state, offset),
                "offset {offset} was wrong when the cache was warm"
            );
            assert_eq!(
                Some(expected),
                location_at(&state(), offset),
                "offset {offset} was wrong when the cache was cold"
            );
        }
    }

    /// Rows can be appended after lookups have already populated the cache.
    #[test]
    fn location_after_appending_source() {
        let mut state = state();
        assert_eq!(Some((4, 3)), location_at(&state, 8));
        state.update_from_source(9, b"\ndddd");
        assert_eq!(Some((4, 3)), location_at(&state, 8));
        assert_eq!(Some((5, 2)), location_at(&state, 11));
        // Resolving an offset that precedes the cached row forces the binary search fallback to run
        // over the grown offset table.
        assert_eq!(Some((2, 2)), location_at(&state, 3));
    }
}
