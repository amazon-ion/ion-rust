enum State {
    Unquoted,
    Quoted(u8),
    LongString,
    LineComment,
    BlockComment,
}

/// Tracks a container's closing delimiter between parser retries. This does not validate Ion;
/// mismatched delimiters and lobs return control to the parser.
pub(crate) struct TextContainerBoundary {
    offset: usize,
    delimiters: Vec<u8>,
    state: State,
}

impl TextContainerBoundary {
    pub(crate) fn new(data: &[u8]) -> Option<Self> {
        let offset = data.iter().position(|b| !b.is_ascii_whitespace())?;
        if !matches!(data[offset], b'[' | b'{' | b'(') {
            return None;
        }
        Some(Self {
            offset,
            delimiters: Vec::new(),
            state: State::Unquoted,
        })
    }

    pub(crate) fn needs_parse(&mut self, data: &[u8]) -> bool {
        while self.offset < data.len() {
            let byte = data[self.offset];
            let rest = &data[self.offset..];
            match self.state {
                State::Quoted(quote) => {
                    if byte == b'\\' {
                        if rest.len() < 2 {
                            break;
                        }
                        self.offset += 2;
                        continue;
                    }
                    if byte == quote {
                        self.state = State::Unquoted;
                    }
                }
                State::LongString => {
                    if byte == b'\\' {
                        if rest.len() < 2 {
                            break;
                        }
                        self.offset += 2;
                        continue;
                    }
                    if byte == b'\'' {
                        if rest.len() < 3 {
                            break;
                        }
                        if rest.starts_with(b"'''") {
                            self.state = State::Unquoted;
                            self.offset += 3;
                            continue;
                        }
                    }
                }
                State::LineComment => {
                    if matches!(byte, b'\n' | b'\r') {
                        self.state = State::Unquoted;
                    }
                }
                State::BlockComment => {
                    if byte == b'*' {
                        if rest.len() < 2 {
                            break;
                        }
                        if rest[1] == b'/' {
                            self.state = State::Unquoted;
                            self.offset += 2;
                            continue;
                        }
                    }
                }
                State::Unquoted => match byte {
                    b'"' => self.state = State::Quoted(b'"'),
                    b'\'' => {
                        if rest.len() < 3 {
                            break;
                        }
                        if rest.starts_with(b"'''") {
                            self.state = State::LongString;
                            self.offset += 3;
                            continue;
                        }
                        self.state = State::Quoted(b'\'');
                    }
                    b'/' => {
                        if rest.len() < 2 {
                            break;
                        }
                        match rest[1] {
                            b'/' => self.state = State::LineComment,
                            b'*' => self.state = State::BlockComment,
                            _ => {
                                self.offset += 1;
                                continue;
                            }
                        }
                        self.offset += 2;
                        continue;
                    }
                    b'[' => self.delimiters.push(b']'),
                    b'(' => self.delimiters.push(b')'),
                    b'{' => {
                        if rest.len() < 2 {
                            break;
                        }
                        if rest[1] == b'{' {
                            return true;
                        }
                        self.delimiters.push(b'}');
                    }
                    b']' | b'}' | b')' => {
                        if self.delimiters.pop() != Some(byte) || self.delimiters.is_empty() {
                            return true;
                        }
                    }
                    _ => {}
                },
            }
            self.offset += 1;
        }
        false
    }
}
