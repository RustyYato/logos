use super::internal::LexerInternal;
use super::Logos;
use crate::source::{self, Source};

use core::cell::Cell;
use core::fmt::{self, Debug};
use core::ops::{Deref, DerefMut};

/// Byte range in the source.
pub type Span = core::ops::Range<usize>;

/// `Lexer` is the main struct of the crate that allows you to read through a
/// `Source` and produce tokens for enums implementing the `Logos` trait.
pub struct Lexer<'source, Token: Logos<'source>> {
    source: &'source Token::Source,
    token: Cell<Option<Result<Token, Token::Error>>>,
    token_start: Cell<usize>,
    token_end: Cell<usize>,

    /// Extras associated with the `Token`.
    pub extras: Token::Extras,
}

impl<'source, Token> Debug for Lexer<'source, Token>
where
    Token: Logos<'source>,
    Token::Source: Debug,
    Token::Extras: Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_map()
            .entry(&"source", &self.source)
            .entry(&"extras", &self.extras)
            .finish()
    }
}

impl<'source, Token: Logos<'source>> Lexer<'source, Token> {
    /// Create a new `Lexer`.
    ///
    /// Due to type inference, it might be more ergonomic to construct
    /// it by calling [`Token::lexer`](./trait.Logos.html#method.lexer) on any `Token` with derived `Logos`.
    pub fn new(source: &'source Token::Source) -> Self
    where
        Token::Extras: Default,
    {
        Self::with_extras(source, Default::default())
    }

    /// Create a new `Lexer` with the provided `Extras`.
    ///
    /// Due to type inference, it might be more ergonomic to construct
    /// it by calling [`Token::lexer_with_extras`](./trait.Logos.html#method.lexer_with_extras) on any `Token` with derived `Logos`.
    pub fn with_extras(source: &'source Token::Source, extras: Token::Extras) -> Self {
        Lexer {
            source,
            token: Cell::new(None),
            extras,
            token_start: Cell::new(0),
            token_end: Cell::new(0),
        }
    }

    /// Source from which this Lexer is reading tokens.
    #[inline]
    pub fn source(&self) -> &'source Token::Source {
        self.source
    }

    /// Wrap the `Lexer` in an [`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html)
    /// that produces tuples of `(Token, `[`Span`](./type.Span.html)`)`.
    ///
    /// # Example
    ///
    /// ```
    /// use logos::Logos;
    ///
    /// #[derive(Debug, PartialEq, Clone, Default)]
    /// enum LexingError {
    ///     NumberParseError,
    ///     #[default]
    ///     Other
    /// }
    ///
    /// impl From<std::num::ParseIntError> for LexingError {
    ///    fn from(_: std::num::ParseIntError) -> Self {
    ///       LexingError::NumberParseError
    ///   }
    /// }
    ///
    /// impl From<std::num::ParseFloatError> for LexingError {
    ///   fn from(_: std::num::ParseFloatError) -> Self {
    ///      LexingError::NumberParseError
    ///   }
    /// }
    ///
    /// #[derive(Logos, Debug, PartialEq)]
    /// #[logos(error = LexingError)]
    /// enum Example {
    ///     #[regex(r"[ \n\t\f]+", logos::skip)]
    ///     Ignored,
    ///
    ///     #[regex("-?[0-9]+", |lex| lex.slice().parse())]
    ///     Integer(i64),
    ///
    ///     #[regex("-?[0-9]+\\.[0-9]+", |lex| lex.slice().parse())]
    ///     Float(f64),
    /// }
    ///
    /// let tokens: Vec<_> = Example::lexer("42 3.14 -5 f").spanned().collect();
    ///
    /// assert_eq!(
    ///     tokens,
    ///     &[
    ///         (Ok(Example::Integer(42)), 0..2),
    ///         (Ok(Example::Float(3.14)), 3..7),
    ///         (Ok(Example::Integer(-5)), 8..10),
    ///         (Err(LexingError::Other), 11..12), // 'f' is not a recognized token
    ///     ],
    /// );
    /// ```
    #[inline]
    pub fn spanned(self) -> SpannedIter<'source, Token> {
        SpannedIter { lexer: self }
    }

    #[inline]
    #[doc(hidden)]
    #[deprecated(since = "0.11.0", note = "please use `span` instead")]
    pub fn range(&self) -> Span {
        self.span()
    }

    /// Get the range for the current token in `Source`.
    #[inline]
    pub fn span(&self) -> Span {
        self.token_start.get()..self.token_end.get()
    }

    /// Get a string slice of the current token.
    #[inline]
    pub fn slice(&self) -> <Token::Source as Source>::Slice<'source> {
        unsafe { self.source.slice_unchecked(self.span()) }
    }

    /// Get a slice of remaining source, starting at the end of current token.
    #[inline]
    pub fn remainder(&self) -> <Token::Source as Source>::Slice<'source> {
        unsafe {
            self.source
                .slice_unchecked(self.token_end.get()..self.source.len())
        }
    }

    /// Turn this lexer into a lexer for a new token type.
    ///
    /// The new lexer continues to point at the same span as the current lexer,
    /// and the current token becomes the error token of the new token type.
    pub fn morph<Token2>(self) -> Lexer<'source, Token2>
    where
        Token2: Logos<'source, Source = Token::Source>,
        Token::Extras: Into<Token2::Extras>,
    {
        Lexer {
            source: self.source,
            token: Cell::new(None),
            extras: self.extras.into(),
            token_start: self.token_start,
            token_end: self.token_end,
        }
    }

    /// Bumps the end of currently lexed token by `n` bytes.
    ///
    /// # Panics
    ///
    /// Panics if adding `n` to current offset would place the `Lexer` beyond the last byte,
    /// or in the middle of an UTF-8 code point (does not apply when lexing raw `&[u8]`).
    pub fn bump(&self, n: usize) {
        let token_end = self.token_end.get() + n;
        assert!(self.source.is_boundary(token_end), "Invalid Lexer bump");
        self.token_end.set(token_end);
    }

    /// Parse the next token
    pub fn lex(&self) -> Option<Result<Token, Token::Error>> {
        self.token_start.set(self.token_end.get());

        Token::lex(self);

        // This basically treats self.token as a temporary field.
        // Since we always immediately return a newly set token here,
        // we don't have to replace it with `None` or manually drop
        // it later.
        self.token.take()
    }
}

impl<'source, Token> Clone for Lexer<'source, Token>
where
    Token: Logos<'source> + Clone,
    Token::Extras: Clone,
{
    fn clone(&self) -> Self {
        let token = self.token.take();
        let token_clone = token.clone();
        self.token.set(token);
        debug_assert!(token_clone.is_none());
        Lexer {
            extras: self.extras.clone(),
            token: Cell::new(token_clone),
            source: self.source,
            token_start: Cell::new(self.token_start.get()),
            token_end: Cell::new(self.token_end.get()),
        }
    }
}

impl<'source, Token> Iterator for Lexer<'source, Token>
where
    Token: Logos<'source>,
{
    type Item = Result<Token, Token::Error>;

    #[inline]
    fn next(&mut self) -> Option<Result<Token, Token::Error>> {
        self.lex()
    }
}

/// Iterator that pairs tokens with their position in the source.
///
/// Look at [`Lexer::spanned`](./struct.Lexer.html#method.spanned) for documentation.
pub struct SpannedIter<'source, Token: Logos<'source>> {
    lexer: Lexer<'source, Token>,
}

// deriving Clone doesn't infer the necessary `Token::Extras: Clone` bound
impl<'source, Token> Clone for SpannedIter<'source, Token>
where
    Token: Logos<'source> + Clone,
    Token::Extras: Clone,
{
    fn clone(&self) -> Self {
        SpannedIter {
            lexer: self.lexer.clone(),
        }
    }
}

impl<'source, Token> Iterator for SpannedIter<'source, Token>
where
    Token: Logos<'source>,
{
    type Item = (Result<Token, Token::Error>, Span);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next().map(|token| (token, self.lexer.span()))
    }
}

impl<'source, Token> Deref for SpannedIter<'source, Token>
where
    Token: Logos<'source>,
{
    type Target = Lexer<'source, Token>;

    fn deref(&self) -> &Lexer<'source, Token> {
        &self.lexer
    }
}

impl<'source, Token> DerefMut for SpannedIter<'source, Token>
where
    Token: Logos<'source>,
{
    fn deref_mut(&mut self) -> &mut Lexer<'source, Token> {
        &mut self.lexer
    }
}

#[doc(hidden)]
/// # WARNING!
///
/// **This trait, and its methods, are not meant to be used outside of the
/// code produced by `#[derive(Logos)]` macro.**
impl<'source, Token> LexerInternal<'source> for Lexer<'source, Token>
where
    Token: Logos<'source>,
{
    type Token = Token;

    /// Read a `Chunk` at current position of the `Lexer`. If end
    /// of the `Source` has been reached, this will return `0`.
    #[inline]
    fn read<Chunk>(&self) -> Option<Chunk>
    where
        Chunk: source::Chunk<'source>,
    {
        self.source.read(self.token_end.get())
    }

    /// Read a `Chunk` at a position offset by `n`.
    #[inline]
    fn read_at<Chunk>(&self, n: usize) -> Option<Chunk>
    where
        Chunk: source::Chunk<'source>,
    {
        self.source.read(self.token_end.get() + n)
    }

    #[inline]
    unsafe fn read_unchecked<Chunk>(&self, n: usize) -> Chunk
    where
        Chunk: source::Chunk<'source>,
    {
        self.source.read_unchecked(self.token_end.get() + n)
    }

    /// Test a chunk at current position with a closure.
    #[inline]
    fn test<T, F>(&self, test: F) -> bool
    where
        T: source::Chunk<'source>,
        F: FnOnce(T) -> bool,
    {
        match self.source.read::<T>(self.token_end.get()) {
            Some(chunk) => test(chunk),
            None => false,
        }
    }

    /// Test a chunk at current position offset by `n` with a closure.
    #[inline]
    fn test_at<T, F>(&self, n: usize, test: F) -> bool
    where
        T: source::Chunk<'source>,
        F: FnOnce(T) -> bool,
    {
        match self.source.read::<T>(self.token_end.get() + n) {
            Some(chunk) => test(chunk),
            None => false,
        }
    }

    /// Bump the position `Lexer` is reading from by `size`.
    #[inline]
    fn bump_unchecked(&self, size: usize) {
        let token_end = self.token_end.get() + size;
        debug_assert!(token_end <= self.source.len(), "Bumping out of bounds!");

        self.token_end.set(token_end);
    }

    /// Reset `token_start` to `token_end`.
    #[inline]
    fn trivia(&self) {
        self.token_start.set(self.token_end.get());
    }

    /// Set the current token to appropriate `#[error]` variant.
    /// Guarantee that `token_end` is at char boundary for `&str`.
    #[inline]
    fn error(&self)
    where
        <Self::Token as crate::Logos<'source>>::Error: Default,
    {
        self.token_end
            .set(self.source.find_boundary(self.token_end.get()));
        self.token.set(Some(Err(Token::Error::default())));
    }

    #[inline]
    fn end(&self) {
        self.token.set(None);
    }

    #[inline]
    fn set(
        &self,
        token: Result<
            Self::Token,
            <<Self as LexerInternal<'source>>::Token as Logos<'source>>::Error,
        >,
    ) {
        self.token.set(Some(token));
    }
}
