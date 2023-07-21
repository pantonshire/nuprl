use std::collections::VecDeque;

#[derive(Debug)]
pub(super) struct TokenStream<T> {
    tokens: VecDeque<T>,
}

impl<T> TokenStream<T> {
    pub(super) fn new(tokens: VecDeque<T>) -> Self {
        Self { tokens }
    }

    pub(super) fn peek(&self) -> Option<&T> {
        self.tokens.front()
    }

    pub(super) fn consume(&mut self) -> Option<T> {
        self.tokens.pop_front()
    }

    pub(super) fn consume_if<P>(&mut self, predicate: P) -> Option<T>
    where
        P: for<'a> FnOnce(&'a T) -> bool,
    {
        if self.peek().map(predicate).unwrap_or(false) {
            self.consume()
        } else {
            None
        }
    }
}
