use std::{format_args as f, io, marker::PhantomData};

use crate::{
    ast::{self, Expr, Typed},
    codegen::x86_64_env,
    types::well_known,
    util::intern::{Interned, Interner},
};

pub struct Generator<'ident, W, E> {
    writer: W,
    ident_interner: &'ident Interner<str>,
    indent: bool,
    _env: PhantomData<E>,
}

impl<W, E> Generator<'_, W, E>
where
    W: io::Write,
    E: x86_64_env::Env,
{
    pub fn new(writer: W, ident_interner: &Interner<str>) -> Generator<'_, W, E> {
        Generator {
            writer,
            ident_interner,
            indent: false,
            _env: PhantomData,
        }
    }

    pub fn generate(mut self, program: &ast::Program<Typed>) {
        self.g_program_prologue();
        self.g_methods(program);
        self.g_vtables(program);
        self.g_data(program);
    }
}

/// Target-specific functions.
impl<W, E> Generator<'_, W, E>
where
    W: io::Write,
    E: x86_64_env::Env,
{
    fn g_program_prologue(&mut self) {
        self.out(E::GLOBAL_PROLOGUE);
    }

    fn g_methods(&mut self, program: &ast::Program<Typed>) {
        self.out(f!(".section {}", E::SECTION_TEXT));

        for class in &program.classes {
            let class_name = self.ident(&class.name);
            self.out(f!("# CLASS {class_name}\n"));

            let methods = class.features.iter().filter_map(|feature| {
                if let ast::Feature::Method(method) = feature {
                    Some(method)
                } else {
                    None
                }
            });

            for method in methods {
                self.g_method(method, class_name);
            }
        }
    }

    fn g_method(&mut self, method: &ast::Method<Typed>, class_name: ResolvedIdent) {
        let method_name = self.ident(method.name);
        let qualified = Self::qualified(class_name, method_name);
        if qualified.is_main() {
            self.out(f!(".global {qualified}"));
        }
        self.out(f!("{qualified}:"));
        self.indented(|this| {
            this.g_method_prologue(method);
            this.g_expr(&method.body);
            this.g_method_epilogue(method);
        });
    }

    #[expect(unused_variables)]
    fn g_expr(&mut self, e: &Expr<Typed>) {
        match &e.kind {
            ast::ExprKind::Assignment {
                target,
                value,
                info,
            } => todo!(),
            ast::ExprKind::Dispatch {
                qualifier,
                method,
                args,
            } => todo!(),
            ast::ExprKind::Conditional {
                predicate,
                then_arm,
                else_arm,
            } => todo!(),
            ast::ExprKind::While { predicate, body } => todo!(),
            ast::ExprKind::Block { body } => todo!(),
            ast::ExprKind::Let { bindings, body } => todo!(),
            ast::ExprKind::Case { predicate, arms } => todo!(),
            ast::ExprKind::New { ty } => todo!(),
            ast::ExprKind::Unary { op, expr } => todo!(),
            ast::ExprKind::Binary { op, lhs, rhs } => todo!(),
            ast::ExprKind::Paren(expr) => todo!(),
            ast::ExprKind::Id(ident, _) => todo!(),
            ast::ExprKind::Int(int) => self.out(f!("mov rax, {int}")),
            ast::ExprKind::String(_) => todo!(),
            ast::ExprKind::Bool(_) => todo!(),
            ast::ExprKind::Dummy => todo!(),
        }
    }

    fn g_method_prologue(&mut self, _method: &ast::Method<Typed>) {
        self.out("push rbp");
        self.out("mov rbp, rsp");
    }

    fn g_method_epilogue(&mut self, _method: &ast::Method<Typed>) {
        self.out("pop rbp");
        self.out("ret");
    }

    #[expect(clippy::unused_self)]
    fn g_vtables(&mut self, _program: &ast::Program<Typed>) {}

    #[expect(clippy::unused_self)]
    fn g_data(&mut self, _program: &ast::Program<Typed>) {}
}

/// Utility functions.
impl<'ident, W, E> Generator<'ident, W, E>
where
    W: io::Write,
    E: x86_64_env::Env,
{
    /// Prints a line.
    fn out(&mut self, f: impl std::fmt::Display) {
        let indent = if self.indent { "    " } else { "" };
        writeln!(self.writer, "{indent}{f}").expect("Failed to write to sink");
    }

    /// Prints an empty line.
    fn out_line(&mut self) {
        writeln!(self.writer).expect("Failed to write to sink");
    }

    /// Resolves an identifier, returning a resolved ident.
    fn ident(&mut self, handle: impl Into<Interned<str>>) -> ResolvedIdent<'ident> {
        let ident = handle.into();
        let name = self.ident_interner.get(ident);
        ResolvedIdent { ident, name }
    }

    fn qualified<'i>(
        class: ResolvedIdent<'i>,
        method: ResolvedIdent<'i>,
    ) -> QualifiedMethod<'i, E> {
        QualifiedMethod {
            class,
            method,
            _env: PhantomData,
        }
    }

    /// Writes in an indented block that is finished with an empty line.
    fn indented<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.indent = true;
        let res = f(self);
        self.indent = false;
        self.out_line();
        res
    }
}

#[derive(Copy, Clone)]
struct QualifiedMethod<'i, E> {
    class: ResolvedIdent<'i>,
    method: ResolvedIdent<'i>,
    _env: PhantomData<E>,
}

impl<E> QualifiedMethod<'_, E> {
    fn is_main(&self) -> bool {
        self.class.ident == well_known::MAIN && self.method.ident == well_known::MAIN_METHOD
    }
}

impl<E> std::fmt::Display for QualifiedMethod<'_, E>
where
    E: x86_64_env::Env,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_main() {
            write!(f, "{}", E::ENTRY_POINT)
        } else {
            let class = self.class.name;
            let method = self.method.name;
            write!(f, ".{class}__{method}")
        }
    }
}

#[derive(Copy, Clone)]
struct ResolvedIdent<'i> {
    ident: Interned<str>,
    name: &'i str,
}

impl std::fmt::Display for ResolvedIdent<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
