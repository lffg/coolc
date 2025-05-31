use crate::util::intern::Interner;

pub mod error;
pub mod tree;

pub struct Context<'ident> {
    pub ident_interner: &'ident Interner<str>,
}

/// Analogous to [`std::fmt::Display`], but also contains the program context,
/// such as the current [`Interner`].
pub trait Show {
    fn show(&self, f: &mut std::fmt::Formatter<'_>, ctx: &Context<'_>) -> std::fmt::Result;

    /// Returns a type which can be displayed.
    fn display(&self, ctx: &Context<'_>) -> impl std::fmt::Display
    where
        Self: Sized,
    {
        Display(self, ctx)
    }
}

struct Display<'this, 'ctx, 'ident, T: Show>(pub &'this T, pub &'ctx Context<'ident>);

impl<T> std::fmt::Display for Display<'_, '_, '_, T>
where
    T: Show,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Display(this, ctx) = self;
        this.show(f, ctx)
    }
}
