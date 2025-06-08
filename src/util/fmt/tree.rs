use std::io::Write;

use crate::{ast::*, types::Type, util::intern::Interner};

const INDENT_WIDTH: usize = 2;

pub fn print_program_string<I: InfoWriter>(idents: &Interner<str>, program: &Program<I>) -> String {
    let mut buf = Vec::with_capacity(1024);
    print_program(&mut buf, idents, program).unwrap();
    String::from_utf8(buf).unwrap()
}

pub fn print_expr_string<I: InfoWriter>(idents: &Interner<str>, expr: &Expr<I>) -> String {
    let mut buf = Vec::with_capacity(512);
    print_expr(&mut buf, idents, 0, expr).unwrap();
    String::from_utf8(buf).unwrap()
}

pub fn print_program<I: InfoWriter>(
    w: &mut impl Write,
    idents: &Interner<str>,
    program: &Program<I>,
) -> std::io::Result<()> {
    for class in &program.classes {
        print_class(w, idents, 0, class)?;
    }
    Ok(())
}

fn print_class<I: InfoWriter>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    class: &Class<I>,
) -> std::io::Result<()> {
    sp(w, i)?;
    write!(w, "class {}", class.name.write(idents))?;
    if let Some(ref inherits) = class.inherits {
        write!(w, " inherits {}", idents.get(inherits))?;
    }
    writeln!(w)?;
    for feature in &class.features {
        print_feature(w, idents, i + 1, feature)?;
    }
    Ok(())
}

fn print_feature<I: InfoWriter>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    feature: &Feature<I>,
) -> std::io::Result<()> {
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
                write!(
                    w,
                    "{}: {}",
                    idents.get(formal.name),
                    formal.ty.write(idents)
                )?;
            }
            write!(w, ") : {}", return_ty.write(idents))?;
            writeln!(w)?;
            print_expr(w, idents, i + 1, body)?;
        }
    }
    Ok(())
}

fn print_binding<I: InfoWriter>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    binding: &Binding<I>,
) -> std::io::Result<()> {
    write!(
        w,
        "{}: {}",
        idents.get(binding.name),
        binding.ty.write(idents),
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

pub fn print_expr<I: InfoWriter>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    expr: &Expr<I>,
) -> std::io::Result<()> {
    sp(w, i)?;
    let info = expr.info.write_resolved(idents); // inferred type, for typed ASTs
    let span = expr.span;
    match &expr.kind {
        ExprKind::Assignment {
            target,
            value,
            info: _,
        } => {
            writeln!(w, "assignment {} ({span}{info})", idents.get(target))?;
            print_expr(w, idents, i + 1, value)?;
        }
        ExprKind::Dispatch {
            qualifier,
            method,
            args,
        } => {
            writeln!(w, "dispatch {} ({span}{info})", idents.get(method))?;

            if let Some(qualifier) = &qualifier {
                sp(w, i + 1)?;
                write!(w, "receiver")?;
                if let Some(static_qualifier) = &qualifier.static_qualifier {
                    write!(w, " @ {}", static_qualifier.write(idents))?;
                }
                writeln!(w)?;
                print_expr(w, idents, i + 2, &qualifier.expr)?;
            }

            if !args.is_empty() {
                sp(w, i + 1)?;
                writeln!(w, "arguments")?;
                for arg in args {
                    print_expr(w, idents, i + 2, arg)?;
                }
            }
        }
        ExprKind::Conditional {
            predicate,
            then_arm,
            else_arm,
        } => {
            writeln!(w, "conditional ({span}{info})")?;
            print_expr(w, idents, i + 1, predicate)?;
            print_expr(w, idents, i + 1, then_arm)?;
            print_expr(w, idents, i + 1, else_arm)?;
        }
        ExprKind::While { predicate, body } => {
            writeln!(w, "while ({span}{info})")?;
            print_expr(w, idents, i + 1, predicate)?;
            print_expr(w, idents, i + 1, body)?;
        }
        ExprKind::Block { body } => {
            writeln!(w, "block ({span}{info})")?;
            for item in body {
                print_expr(w, idents, i + 1, item)?;
            }
        }
        ExprKind::Let { bindings, body } => {
            writeln!(w, "let ({span}{info})")?;
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
            writeln!(w, "case ({span}{info})")?;
            print_expr(w, idents, i + 1, predicate)?;
            for arm in arms {
                print_case_arm(w, idents, i + 1, arm)?;
            }
        }
        ExprKind::New { ty } => {
            let ty = ty.write(idents);
            writeln!(w, "new {ty} ({span}{info})")?;
        }
        ExprKind::Unary {
            op,
            expr: inner_expr,
        } => {
            writeln!(w, "unary {op:?} ({span}{info})")?;
            print_expr(w, idents, i + 1, inner_expr)?;
        }
        ExprKind::Binary { op, lhs, rhs } => {
            writeln!(w, "binary {op:?} ({span}{info})")?;
            print_expr(w, idents, i + 1, lhs)?;
            print_expr(w, idents, i + 1, rhs)?;
        }
        ExprKind::Paren(inner_expr) => {
            writeln!(w, "paren ({span}{info})")?;
            print_expr(w, idents, i + 1, inner_expr)?;
        }
        ExprKind::Id(ident, _) => {
            writeln!(w, "ident {} ({span}{info})", idents.get(ident))?;
        }
        ExprKind::Int(val) => {
            writeln!(w, "int {val} ({span}{info})")?;
        }
        ExprKind::String(val) => {
            writeln!(w, "string {val:?} ({span}{info})")?;
        }
        ExprKind::Bool(val) => {
            writeln!(w, "bool {val} ({span}{info})")?;
        }
        ExprKind::Dummy => {
            writeln!(w, "dummy ({span}{info})")?;
        }
    }
    Ok(())
}

fn print_case_arm<I: InfoWriter>(
    w: &mut impl Write,
    idents: &Interner<str>,
    i: usize,
    arm: &CaseArm<I>,
) -> std::io::Result<()> {
    sp(w, i)?;
    writeln!(
        w,
        "arm {}: {} =>",
        idents.get(arm.name),
        arm.ty.write(idents),
    )?;
    print_expr(w, idents, i + 1, &arm.body)?;
    Ok(())
}

fn sp(w: &mut impl Write, i: usize) -> std::io::Result<()> {
    write!(w, "{:width$}", "", width = i * INDENT_WIDTH)
}

pub trait InfoWriter: Info<Ty: NameWriter, Expr: NameWriter> {}

impl<I> InfoWriter for I
where
    I: Info,
    I::Ty: NameWriter,
    I::Expr: NameWriter,
{
}

pub trait NameWriter {
    fn write<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i;

    fn write_resolved<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        _ = idents;
        ""
    }
}

impl NameWriter for () {
    fn write<'i>(&self, _: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        ""
    }
}

impl NameWriter for TypeName {
    fn write<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        idents.get(self.name())
    }
}

impl NameWriter for Type {
    fn write<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        idents.get(self.name())
    }

    fn write_resolved<'i>(&self, idents: &'i Interner<str>) -> impl std::fmt::Display + 'i {
        pub struct TypeWriter<'a>(&'a str);

        impl std::fmt::Display for TypeWriter<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, " %: {}", self.0)
            }
        }

        TypeWriter(idents.get(self.name()))
    }
}
