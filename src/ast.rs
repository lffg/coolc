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

use crate::{token::Span, types::builtins, util::intern::Interned};

#[derive(Debug, PartialEq, Default)]
pub struct Program<T = TypeName> {
    pub classes: Vec<Class<T>>,
}

#[derive(Debug, PartialEq)]
pub struct Class<T = TypeName> {
    pub name: T,
    /// Actual inheritance can be accessed through [`TypedClass::name`]'s
    /// [`Type::parent`], if typed.
    ///
    /// This field always preserves the original source declaration.
    pub inherits: Option<TypeName>,
    pub features: Vec<Feature<T>>,
}

#[derive(Debug, PartialEq)]
pub enum Feature<T = TypeName> {
    Attribute(Binding<T>),
    Method(Method<T>),
}

#[derive(Debug, PartialEq)]
pub struct Binding<T = TypeName> {
    pub name: Ident,
    pub ty: T,
    pub initializer: Option<Expr<T>>,
}

#[derive(Debug, PartialEq)]
pub struct Method<T = TypeName> {
    pub name: Ident,
    /// List of parameters ("formal parameters").
    pub formals: Vec<Formal<T>>,
    pub return_ty: T,
    pub body: Expr<T>,
}

pub struct MethodSignature<T> {
    pub name: Ident,
    pub formals: Vec<Formal<T>>,
    pub return_ty: T,
}

impl<T> From<Method<T>> for MethodSignature<T> {
    fn from(method: Method<T>) -> Self {
        MethodSignature {
            name: method.name,
            formals: method.formals,
            return_ty: method.return_ty,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Formal<T = TypeName> {
    pub name: Ident,
    pub ty: T,
}

#[derive(Debug, PartialEq)]
pub struct Expr<T = TypeName> {
    pub kind: ExprKind<T>,
    pub span: Span,
    pub ty: T,
}

impl<T> Expr<T> {
    pub fn dummy(span: Span) -> Expr<T>
    where
        T: Default,
    {
        Expr {
            kind: ExprKind::Dummy,
            span,
            ty: T::default(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ExprKind<T = TypeName> {
    Assignment {
        target: Ident,
        value: Box<Expr<T>>,
    },
    Dispatch {
        qualifier: Option<DispatchQualifier<T>>,
        method: Ident,
        args: Vec<Expr<T>>,
    },
    Conditional {
        predicate: Box<Expr<T>>,
        then_arm: Box<Expr<T>>,
        else_arm: Box<Expr<T>>,
    },
    While {
        predicate: Box<Expr<T>>,
        body: Box<Expr<T>>,
    },
    /// AKA: Sequence
    Block {
        /// Non empty list of expressions.
        body: Vec<Expr<T>>,
    },
    Let {
        /// Non empty list of bindings.
        bindings: Vec<Binding<T>>,
        body: Box<Expr<T>>,
    },
    Case {
        predicate: Box<Expr<T>>,
        /// Non empty list of arms.
        arms: Vec<CaseArm<T>>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expr<T>>,
    },
    Binary {
        op: BinaryOperator,
        lhs: Box<Expr<T>>,
        rhs: Box<Expr<T>>,
    },
    Paren(Box<Expr<T>>),
    Id(Ident),
    Int(i64),
    String(Box<str>),
    Bool(bool),
    Dummy,
}

#[derive(Debug, PartialEq)]
pub struct DispatchQualifier<T = TypeName> {
    pub expr: Box<Expr<T>>,
    pub ty: T,
}

#[derive(Debug, PartialEq)]
pub struct CaseArm<T = TypeName> {
    pub name: Ident,
    pub ty: T,
    pub body: Box<Expr<T>>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum UnaryOperator {
    New,
    IsVoid,
    /// AKA Negation (of integers)
    Inverse,
    Not,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Le,
    Leq,
}

#[derive(Copy, Clone, Debug, PartialEq)]
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

#[derive(Copy, Clone, Debug, PartialEq)]
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

#[cfg(test)]
pub(crate) mod test_utils {
    use crate::types::well_known;

    use super::*;

    pub fn from_expr_to_main_program(expr: Expr<TypeName>) -> Program<TypeName> {
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

    pub fn from_main_program_to_expr<T>(mut prog: Program<T>) -> Expr<T>
    where
        T: Into<Interned<str>>,
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
