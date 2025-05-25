use crate::{ast::*, util::intern::Interner};
use std::io::Write;

const INDENT_WIDTH: usize = 2;

fn sp(w: &mut impl Write, i: usize) -> std::io::Result<()> {
    write!(w, "{:width$}", "", width = i * INDENT_WIDTH)
}

pub fn print_program_string(idents: &Interner<str>, program: &Program) -> String {
    let mut buf = Vec::with_capacity(1024);
    print_program(&mut buf, idents, program).unwrap();
    String::from_utf8(buf).unwrap()
}

pub fn print_expr_string(idents: &Interner<str>, expr: &Expr) -> String {
    let mut buf = Vec::with_capacity(512);
    print_expr(&mut buf, idents, 0, expr).unwrap();
    String::from_utf8(buf).unwrap()
}

pub fn print_program(
    w: &mut impl Write,
    idents: &Interner<str>,
    program: &Program,
) -> std::io::Result<()> {
    for class in &program.classes {
        print_class(w, idents, 0, class)?;
    }
    Ok(())
}

fn print_class(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    class: &Class,
) -> std::io::Result<()> {
    sp(w, i)?;
    write!(w, "class {}", idents.get(class.name))?;
    if let Some(ref inherits) = class.inherits {
        write!(w, " inherits {}", idents.get(inherits))?;
    }
    writeln!(w)?;
    for feature in &class.features {
        print_feature(w, idents, i + 1, feature)?;
    }
    Ok(())
}

fn print_feature(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    feature: &Feature,
) -> std::io::Result<()> {
    match feature {
        Feature::Attribute(binding) => {
            sp(w, i)?;
            write!(w, "attribute ")?;
            print_binding(w, idents, i, binding)?;
        }
        Feature::Method {
            name,
            formals,
            return_ty,
            body,
        } => {
            sp(w, i)?;
            write!(w, "method {}(", idents.get(name))?;
            for (idx, formal) in formals.iter().enumerate() {
                if idx > 0 {
                    write!(w, ", ")?;
                }
                write!(
                    w,
                    "{}: {}",
                    idents.get(formal.name),
                    idents.get(formal.ty)
                )?;
            }
            write!(w, ") : {}", idents.get(return_ty))?;
            writeln!(w)?;
            print_expr(w, idents, i + 1, body)?;
        }
    }
    Ok(())
}

fn print_binding(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    binding: &Binding,
) -> std::io::Result<()> {
    write!(
        w,
        "{}: {}",
        idents.get(binding.name),
        idents.get(binding.ty)
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

pub fn print_expr(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    expr: &Expr,
) -> std::io::Result<()> {
    sp(w, i)?;
    let span = expr.span;
    match &expr.kind {
        ExprKind::Assignment { target, value } => {
            writeln!(w, "assignment {} ({span})", idents.get(target))?;
            print_expr(w, idents, i + 1, value)?;
        }
        ExprKind::Dispatch {
            qualifier,
            method,
            args,
        } => {
            writeln!(w, "dispatch {} ({span})", idents.get(method))?;
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
            writeln!(w, "conditional ({span})")?;
            print_expr(w, idents, i + 1, predicate)?;
            print_expr(w, idents, i + 1, then_arm)?;
            print_expr(w, idents, i + 1, else_arm)?;
        }
        ExprKind::While { predicate, body } => {
            writeln!(w, "while ({span})")?;
            print_expr(w, idents, i + 1, predicate)?;
            print_expr(w, idents, i + 1, body)?;
        }
        ExprKind::Block { body } => {
            writeln!(w, "block ({span})")?;
            for item in body {
                print_expr(w, idents, i + 1, item)?;
            }
        }
        ExprKind::Let { bindings, body } => {
            writeln!(w, "let ({span})")?;
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
            writeln!(w, "case ({span})")?;
            print_expr(w, idents, i + 1, predicate)?;
            for arm in arms {
                print_case_arm(w, idents, i + 1, arm)?;
            }
        }
        ExprKind::Unary {
            op,
            expr: inner_expr,
        } => {
            writeln!(w, "unary {op:?} ({span})")?;
            print_expr(w, idents, i + 1, inner_expr)?;
        }
        ExprKind::Binary { op, lhs, rhs } => {
            writeln!(w, "binary {op:?} ({span})")?;
            print_expr(w, idents, i + 1, lhs)?;
            print_expr(w, idents, i + 1, rhs)?;
        }
        ExprKind::Paren(inner_expr) => {
            writeln!(w, "paren ({span})")?;
            print_expr(w, idents, i + 1, inner_expr)?;
        }
        ExprKind::Id(ident) => {
            writeln!(w, "ident {} ({span})", idents.get(ident))?;
        }
        ExprKind::Int(val) => {
            writeln!(w, "int {val} ({span})")?;
        }
        ExprKind::String(val) => {
            writeln!(w, "string {val:?}")?;
        }
        ExprKind::Bool(val) => {
            writeln!(w, "bool {val} ({span})")?;
        }
        ExprKind::Dummy => {
            writeln!(w, "dummy ({span})")?;
        }
    }
    Ok(())
}

fn print_dispatch_qualifier(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    qual: &DispatchQualifier,
) -> std::io::Result<()> {
    sp(w, i)?;
    writeln!(w, "qualifier @ {}", idents.get(qual.ty))?; // Indicate type association
    print_expr(w, idents, i + 1, &qual.expr)?; // Print the actual expression indented
    Ok(())
}

fn print_case_arm(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    arm: &CaseArm,
) -> std::io::Result<()> {
    sp(w, i)?;
    writeln!(
        w,
        "arm {}: {} =>",
        idents.get(arm.name),
        idents.get(arm.ty)
    )?;
    print_expr(w, idents, i + 1, &arm.body)?;
    Ok(())
}
