// program ::= (class ';')+
// class ::= class TYPE [inherits TYPE] '{' feature* '}'
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
// ~ isvoid */ +-
// <= < = not
// <-

use crate::token::Span;

pub struct Program {
    pub classes: Vec<Class>,
}

pub struct Class {
    pub name: Type,
    pub inherits: Option<Type>,
    pub features: Vec<Feature>,
}

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

pub struct Binding {
    pub name: Ident,
    pub ty: Type,
    pub initializer: Option<Expr>,
}

pub struct Formal {
    pub name: Ident,
    pub ty: Type,
}

pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

pub enum ExprKind {
    Assignment {
        name: Ident,
        ty: Type,
    },
    Dispatch {
        qualifier: Option<DispatchQualifier>,
        ident: Ident,
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
    String(String),
    Bool(bool),
}

pub struct DispatchQualifier {
    pub expr: Box<Expr>,
    pub ty: Type,
}

pub struct CaseArm {
    pub name: Ident,
    pub ty: Type,
    pub body: Box<Expr>,
}

pub enum UnaryOperator {
    New,
    IsVoid,
    Inverse,
    Not,
}

pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Le,
    Leq,
}

pub struct Type(pub Ident);

pub struct Ident {
    pub ident: Box<str>,
    pub span: Span,
}
