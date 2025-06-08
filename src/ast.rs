// program ::= (class ';')+
// class ::= class TYPE [inherits TYPE] '{' (feature;) * '}'
// feature ::= ID '(' [formal (',' formal)*] ')' ':' TYPE '{' expr '}'
//           | ID ':' TYPE [<- expr]
// formal ::= ID ':' TYPE
// expr ::= ID [<- expr]
//        | expr '@' TYPE '.' ID '(' [expr (',' expr)*] ')'
//        | ID '(' [expr (',' expr)*] ')'
//        | if expr then expr else expr fi
//        | while expr loop expr pool
//        | '{' expr ';' + '}'
//        | let ID ':' TYPE [<- expr] (',' ID ':' TYPE [<- expr])* in expr
//        | case expr of (ID ':' TYPE '=>' expr ';')+ esac
//        | new TYPE
//        | isvoid expr
//        | expr '+' expr
//        | expr '-' expr
//        | expr '*' expr
//        | expr '/' expr
//        | '~' expr
//        | expr '<' expr
//        | expr '<=' expr
//        | expr '=' expr
//        | not expr
//        | '(' expr ')'
//        | ID
//        | integer
//        | string
//        | true
//        | false

// Precedence
//
// .
// @
// ~
// isvoid
// * /
// + -
// <= < =
// not
// <-

use std::fmt::Debug;

use crate::{
    token::Span,
    type_checker::Symbol,
    types::{builtins, Type},
    util::intern::Interned,
};

/// Info trait which allows one to attach additional information to some of the
/// AST nodes. Inspired by the "Trees that Grow" paper.
pub trait Info {
    type Ty: Clone + Default + Debug;

    type Expr: Clone + Debug;

    type Assignment: Clone + Debug;
    type Id: Clone + Debug;
}

/// Untyped AST.
#[derive(Copy, Clone, Default, Debug)]
pub struct Untyped;

impl Info for Untyped {
    type Ty = TypeName;
    type Expr = ();
    type Assignment = ();
    type Id = ();
}

/// Typed AST.
#[derive(Copy, Clone, Default, Debug)]
pub struct Typed;

impl Info for Typed {
    type Ty = Type;
    type Expr = Type;
    type Assignment = Symbol;
    type Id = Symbol;
}

#[derive(Debug, Default)]
pub struct Program<I: Info> {
    pub classes: Vec<Class<I>>,
}

#[derive(Debug, Clone)]
pub struct Class<I: Info> {
    pub name: I::Ty,
    /// In typed class, actual inherited parent can be accessed through
    /// [`Class::name`]'s [`crate::types::Type::parent`] field (if typed).
    ///
    /// This field always preserves the original source declaration.
    pub inherits: Option<TypeName>,
    pub features: Vec<Feature<I>>,
}

#[derive(Debug, Clone)]
pub enum Feature<I: Info> {
    Attribute(Binding<I>),
    Method(Method<I>),
}

#[derive(Debug, Clone)]
pub struct Binding<I: Info> {
    pub name: Ident,
    pub ty: I::Ty,
    pub initializer: Option<Expr<I>>,
}

#[derive(Debug, Clone)]
pub struct Method<I: Info> {
    pub name: Ident,
    /// List of parameters ("formal parameters").
    pub formals: Vec<Formal<I>>,
    pub return_ty: I::Ty,
    pub body: Expr<I>,
}

#[derive(Debug, Clone)]
pub struct Formal<I: Info> {
    pub name: Ident,
    pub ty: I::Ty,
}

#[derive(Debug, Clone)]
pub struct Expr<I: Info> {
    pub kind: ExprKind<I>,
    pub span: Span,
    pub info: I::Expr,
}

impl<I: Info<Expr = Type>> Expr<I> {
    /// Returns the expression's type.
    pub fn ty(&self) -> &Type {
        &self.info
    }
}

impl<I: Info> Expr<I> {
    pub fn dummy(span: Span) -> Expr<I>
    where
        I::Expr: Default,
    {
        Expr {
            kind: ExprKind::Dummy,
            span,
            info: I::Expr::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind<I: Info> {
    Assignment {
        target: Ident,
        value: Box<Expr<I>>,
        info: I::Assignment,
    },
    Dispatch {
        qualifier: Option<DispatchQualifier<I>>,
        method: Ident,
        args: Vec<Expr<I>>,
    },
    Conditional {
        predicate: Box<Expr<I>>,
        then_arm: Box<Expr<I>>,
        else_arm: Box<Expr<I>>,
    },
    While {
        predicate: Box<Expr<I>>,
        body: Box<Expr<I>>,
    },
    /// AKA: Sequence
    Block {
        /// Non empty list of expressions.
        body: Vec<Expr<I>>,
    },
    Let {
        /// Non empty list of bindings.
        bindings: Vec<Binding<I>>,
        body: Box<Expr<I>>,
    },
    Case {
        predicate: Box<Expr<I>>,
        /// Non empty list of arms.
        arms: Vec<CaseArm<I>>,
    },
    New {
        ty: I::Ty,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expr<I>>,
    },
    Binary {
        op: BinaryOperator,
        lhs: Box<Expr<I>>,
        rhs: Box<Expr<I>>,
    },
    Paren(Box<Expr<I>>),
    Id(Ident, I::Id),
    Int(i64),
    String(Box<str>),
    Bool(bool),
    Dummy,
}

#[derive(Debug, Clone)]
pub struct DispatchQualifier<I: Info> {
    pub expr: Box<Expr<I>>,
    pub static_qualifier: Option<I::Ty>,
}

#[derive(Debug, Clone)]
pub struct CaseArm<I: Info> {
    pub name: Ident,
    pub ty: I::Ty,
    pub body: Box<Expr<I>>,
}

#[derive(Copy, Clone, Debug)]
pub enum UnaryOperator {
    IsVoid,
    /// AKA Negation (of integers)
    Inverse,
    Not,
}

#[derive(Copy, Clone, Debug)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Le,
    Leq,
}

#[derive(Copy, Clone, Debug)]
pub struct TypeName(pub Ident);

impl Default for TypeName {
    fn default() -> Self {
        TypeName::new(builtins::NO_TYPE, builtins::SPAN)
    }
}

impl TypeName {
    pub const fn new(name: Interned<str>, span: Span) -> TypeName {
        TypeName(Ident { name, span })
    }

    pub fn name(&self) -> Interned<str> {
        self.0.name
    }

    pub fn span(&self) -> Span {
        self.0.span
    }
}

impl From<TypeName> for Interned<str> {
    fn from(value: TypeName) -> Self {
        value.0.name
    }
}

impl From<&TypeName> for Interned<str> {
    fn from(value: &TypeName) -> Self {
        value.0.name
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Ident {
    pub name: Interned<str>,
    pub span: Span,
}

impl From<Ident> for Interned<str> {
    fn from(value: Ident) -> Self {
        value.name
    }
}

impl From<&Ident> for Interned<str> {
    fn from(value: &Ident) -> Self {
        value.name
    }
}

pub mod desugar {
    use super::*;

    pub fn multi_binding_let<I>(
        bindings: Vec<Binding<I>>,
        mut body: Box<Expr<I>>,
        span: Span,
        info: &I::Expr,
    ) -> Expr<I>
    where
        I: Info,
    {
        for binding in bindings.into_iter().rev() {
            body = Box::new(Expr {
                kind: ExprKind::Let {
                    bindings: vec![binding],
                    body,
                },
                span,
                info: info.clone(),
            });
        }
        *body
    }
}

#[cfg(test)]
pub(crate) mod test_utils {
    use crate::types::well_known;

    use super::*;

    pub fn from_expr_to_main_program(expr: Expr<Untyped>) -> Program<Untyped> {
        Program {
            classes: vec![Class {
                name: TypeName::new(well_known::MAIN, builtins::SPAN),
                inherits: None,
                features: vec![Feature::Method(Method {
                    name: Ident {
                        name: well_known::MAIN_METHOD,
                        span: builtins::SPAN,
                    },
                    formals: vec![],
                    return_ty: TypeName::new(builtins::OBJECT, builtins::SPAN),
                    body: expr,
                })],
            }],
        }
    }

    pub fn from_main_program_to_expr<I>(mut prog: Program<I>) -> Expr<I>
    where
        I: Info,
        I::Ty: Into<Interned<str>>,
    {
        assert_eq!(prog.classes.len(), 1);
        let mut class = prog.classes.remove(0);
        let name: Interned<str> = class.name.into();
        assert_eq!(name, well_known::MAIN);
        assert_eq!(class.features.len(), 1);
        let Feature::Method(method) = class.features.remove(0) else {
            panic!()
        };
        assert_eq!(method.name.name, well_known::MAIN_METHOD);
        method.body
    }
}
