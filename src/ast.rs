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

use std::fmt;

use crate::token::Span;

#[derive(Debug, PartialEq, Default)]
pub struct Program {
    pub classes: Vec<Class>,
}

impl Program {
    pub fn dummy() -> Program {
        Program {
            classes: Vec::new(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Class {
    pub name: Type,
    pub inherits: Option<Type>,
    pub features: Vec<Feature>,
}

#[derive(Debug, PartialEq)]
pub enum Feature {
    Attribute(Binding),
    Method {
        name: Ident,
        /// List of parameters ("formal parameters").
        formals: Vec<Formal>,
        return_ty: Type,
        body: Expr,
    },
}

#[derive(Debug, PartialEq)]
pub struct Binding {
    pub name: Ident,
    pub ty: Type,
    pub initializer: Option<Expr>,
}

#[derive(Debug, PartialEq)]
pub struct Formal {
    pub name: Ident,
    pub ty: Type,
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn dummy(span: Span) -> Expr {
        Expr {
            kind: ExprKind::Dummy,
            span,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    Assignment {
        target: Ident,
        value: Box<Expr>,
    },
    Dispatch {
        qualifier: Option<DispatchQualifier>,
        method: Ident,
        args: Vec<Expr>,
    },
    Conditional {
        predicate: Box<Expr>,
        then_arm: Box<Expr>,
        else_arm: Box<Expr>,
    },
    While {
        predicate: Box<Expr>,
        body: Box<Expr>,
    },
    Block {
        /// Non empty list of expressions.
        body: Vec<Expr>,
    },
    Let {
        /// Non empty list of bindings.
        bindings: Vec<Binding>,
        body: Box<Expr>,
    },
    Case {
        predicate: Box<Expr>,
        /// Non empty list of arms.
        arms: Vec<CaseArm>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expr>,
    },
    Binary {
        op: BinaryOperator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Paren(Box<Expr>),
    Id(Ident),
    Int(i64),
    String(Box<str>),
    Bool(bool),
    Dummy,
}

#[derive(Debug, PartialEq)]
pub struct DispatchQualifier {
    pub expr: Box<Expr>,
    pub ty: Type,
}

#[derive(Debug, PartialEq)]
pub struct CaseArm {
    pub name: Ident,
    pub ty: Type,
    pub body: Box<Expr>,
}

#[derive(Debug, PartialEq)]
pub enum UnaryOperator {
    New,
    IsVoid,
    Inverse,
    Not,
}

#[derive(Debug, PartialEq)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Le,
    Leq,
}

#[derive(Debug, PartialEq)]
pub struct Type(pub Ident);

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, PartialEq)]
pub struct Ident {
    pub ident: Box<str>,
    pub span: Span,
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ident)?;
        if f.alternate() {
            write!(f, " {:?}", self.span)?;
        }
        Ok(())
    }
}
