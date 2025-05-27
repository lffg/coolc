use crate::{
    ast::*,
    types::Type,
    util::intern::{Interned, Interner},
};
use std::io::Write;

const INDENT_WIDTH: usize = 2;

pub trait Typed {
    fn write<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i;
}

impl Typed for TypeName {
    fn write<'i>(&self, _: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        ""
    }
}

impl Typed for Type {
    fn write<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        TypeWriter(idents.get(self.name()))
    }
}

pub struct TypeWriter<'a>(&'a str);

impl std::fmt::Display for TypeWriter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, " %: {}", self.0)
    }
}

fn sp(w: &mut impl Write, i: usize) -> std::io::Result<()> {
    write!(w, "{:width$}", "", width = i * INDENT_WIDTH)
}

pub fn print_program_string<T: Typed>(idents: &Interner<str>, program: &Program<T>) -> String
where
    for<'a> &'a T: Into<Interned<str>>,
{
    let mut buf = Vec::with_capacity(1024);
    print_program(&mut buf, idents, program).unwrap();
    String::from_utf8(buf).unwrap()
}

pub fn print_expr_string<T: Typed>(idents: &Interner<str>, expr: &Expr<T>) -> String
where
    for<'a> &'a T: Into<Interned<str>>,
{
    let mut buf = Vec::with_capacity(512);
    print_expr(&mut buf, idents, 0, expr).unwrap();
    String::from_utf8(buf).unwrap()
}

pub fn print_program<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    program: &Program<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    for class in &program.classes {
        print_class(w, idents, 0, class)?;
    }
    Ok(())
}

fn print_class<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    class: &Class<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    sp(w, i)?;
    write!(w, "class {}", idents.get(&class.name))?;
    if let Some(ref inherits) = class.inherits {
        write!(w, " inherits {}", idents.get(inherits))?;
    }
    writeln!(w)?;
    for feature in &class.features {
        print_feature(w, idents, i + 1, feature)?;
    }
    Ok(())
}

fn print_feature<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    feature: &Feature<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    match feature {
        Feature::Attribute(binding) => {
            sp(w, i)?;
            write!(w, "attribute ")?;
            print_binding(w, idents, i, binding)?;
        }
        Feature::Method(Method {
            name,
            formals,
            return_ty,
            body,
        }) => {
            sp(w, i)?;
            write!(w, "method {}(", idents.get(name))?;
            for (idx, formal) in formals.iter().enumerate() {
                if idx > 0 {
                    write!(w, ", ")?;
                }
                write!(w, "{}: {}", idents.get(formal.name), idents.get(&formal.ty))?;
            }
            write!(w, ") : {}", idents.get(return_ty))?;
            writeln!(w)?;
            print_expr(w, idents, i + 1, body)?;
        }
    }
    Ok(())
}

fn print_binding<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    binding: &Binding<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    write!(
        w,
        "{}: {}",
        idents.get(binding.name),
        idents.get(&binding.ty)
    )?;
    if let Some(ref initializer) = binding.initializer {
        write!(w, " (initialized)")?;
        writeln!(w)?;
        print_expr(w, idents, i + 1, initializer)?;
    } else {
        writeln!(w)?;
    }
    Ok(())
}

pub fn print_expr<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    expr: &Expr<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    sp(w, i)?;
    let ty = expr.ty.write(idents); // inferred type
    let span = expr.span;
    match &expr.kind {
        ExprKind::Assignment { target, value } => {
            writeln!(w, "assignment {} ({span}{ty})", idents.get(target))?;
            print_expr(w, idents, i + 1, value)?;
        }
        ExprKind::Dispatch {
            qualifier,
            method,
            args,
        } => {
            writeln!(w, "dispatch {} ({span}{ty})", idents.get(method))?;
            if let Some(ref qual) = qualifier {
                print_dispatch_qualifier(w, idents, i + 1, qual)?;
            }
            // Just list arguments indented
            for arg in args {
                print_expr(w, idents, i + 1, arg)?;
            }
        }
        ExprKind::Conditional {
            predicate,
            then_arm,
            else_arm,
        } => {
            writeln!(w, "conditional ({span}{ty})")?;
            print_expr(w, idents, i + 1, predicate)?;
            print_expr(w, idents, i + 1, then_arm)?;
            print_expr(w, idents, i + 1, else_arm)?;
        }
        ExprKind::While { predicate, body } => {
            writeln!(w, "while ({span}{ty})")?;
            print_expr(w, idents, i + 1, predicate)?;
            print_expr(w, idents, i + 1, body)?;
        }
        ExprKind::Block { body } => {
            writeln!(w, "block ({span}{ty})")?;
            for item in body {
                print_expr(w, idents, i + 1, item)?;
            }
        }
        ExprKind::Let { bindings, body } => {
            writeln!(w, "let ({span}{ty})")?;
            for binding in bindings {
                sp(w, i + 1)?;
                write!(w, "binding ")?;
                print_binding(w, idents, i + 1, binding)?;
            }
            sp(w, i + 1)?;
            writeln!(w, "in")?;
            print_expr(w, idents, i + 2, body)?;
        }
        ExprKind::Case { predicate, arms } => {
            writeln!(w, "case ({span}{ty})")?;
            print_expr(w, idents, i + 1, predicate)?;
            for arm in arms {
                print_case_arm(w, idents, i + 1, arm)?;
            }
        }
        ExprKind::Unary {
            op,
            expr: inner_expr,
        } => {
            writeln!(w, "unary {op:?} ({span}{ty})")?;
            print_expr(w, idents, i + 1, inner_expr)?;
        }
        ExprKind::Binary { op, lhs, rhs } => {
            writeln!(w, "binary {op:?} ({span}{ty})")?;
            print_expr(w, idents, i + 1, lhs)?;
            print_expr(w, idents, i + 1, rhs)?;
        }
        ExprKind::Paren(inner_expr) => {
            writeln!(w, "paren ({span}{ty})")?;
            print_expr(w, idents, i + 1, inner_expr)?;
        }
        ExprKind::Id(ident) => {
            writeln!(w, "ident {} ({span}{ty})", idents.get(ident))?;
        }
        ExprKind::Int(val) => {
            writeln!(w, "int {val} ({span}{ty})")?;
        }
        ExprKind::String(val) => {
            writeln!(w, "string {val:?} ({span}{ty})")?;
        }
        ExprKind::Bool(val) => {
            writeln!(w, "bool {val} ({span}{ty})")?;
        }
        ExprKind::Dummy => {
            writeln!(w, "dummy ({span}{ty})")?;
        }
    }
    Ok(())
}

fn print_dispatch_qualifier<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    qual: &DispatchQualifier<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    sp(w, i)?;
    writeln!(w, "qualifier @ {}", idents.get(&qual.ty))?; // Indicate type association
    print_expr(w, idents, i + 1, &qual.expr)?; // Print the actual expression indented
    Ok(())
}

fn print_case_arm<T: Typed>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    arm: &CaseArm<T>,
) -> std::io::Result<()>
where
    for<'a> &'a T: Into<Interned<str>>,
{
    sp(w, i)?;
    writeln!(
        w,
        "arm {}: {} =>",
        idents.get(arm.name),
        idents.get(&arm.ty)
    )?;
    print_expr(w, idents, i + 1, &arm.body)?;
    Ok(())
}
