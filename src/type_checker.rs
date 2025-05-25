use std::collections::HashMap;

use crate::{
    ast::{Program, TypeName},
    token::{Span, Spanned},
    types::{builtins, Type, TypeRegistry},
    util::intern::Interned,
};

type Result<T, E = ()> = std::result::Result<T, E>;

pub type ParseResult<T> = Result<T, (T, Vec<Spanned<Error>>)>;

pub struct Checker {
    registry: TypeRegistry,
    errors: Vec<Spanned<Error>>,
}

impl Checker {
    pub fn with_capacity(capacity: usize) -> Checker {
        Checker {
            registry: TypeRegistry::with_capacity(capacity),
            errors: Vec::with_capacity(8),
        }
    }

    pub fn check(mut self, program: Program) -> (Program, TypeRegistry) {
        self.build_type_registry(&program);

        (program, self.registry)
    }

    /// Scans through the program's source and records all classes in the
    /// `registry` field.
    fn build_type_registry(&mut self, program: &Program) {
        // Maps a class name to its definition span and parent class, if any.
        let mut map: HashMap<Interned<str>, (Span, Option<TypeName>)> =
            HashMap::with_capacity(self.registry.capacity());

        // Define built-ins.
        //
        // This will also help preventing built-in redefinition due to the
        // check in the next section.
        for &(handle, _, parent_handle) in builtins::ALL {
            let parent_name = parent_handle.map(|name| TypeName::new(name, builtins::SPAN));
            map.insert(handle, (builtins::SPAN, parent_name));
        }

        // Build the map from the source and report any duplicate type
        // definition error, if any.
        for class in &program.classes {
            let class_name = Interned::from(class.name);
            let current_span = class.name.span();

            if map.contains_key(&class_name) {
                let (other_span, _) = map[&class_name];
                let error = Error::DuplicateTypeDefinition {
                    name: class_name,
                    other_definition_span: other_span,
                };
                self.errors.push(current_span.wrap(error));
            }

            let val = (current_span, class.inherits);
            map.insert(class.name.into(), val);
        }

        // Declare all types.
        for (class_name, (definition_span, parent_class)) in &map {
            self.define_class(&map, *class_name, *definition_span, {
                // If the source doesn't define a parent class, object is
                // implied.
                const OBJECT: TypeName = TypeName::new(builtins::OBJECT, builtins::SPAN);
                let parent_class = parent_class.unwrap_or(OBJECT);
                Some(parent_class)
            });
        }
    }

    fn define_class(
        &mut self,
        map: &ClassDefinitionMap,
        name: Interned<str>,
        span: Span,
        parent: Option<TypeName>,
    ) -> Type {
        // If this class' parent is not defined, define it first.
        let parent = parent.map(|parent| {
            if let Some(parent_type) = self.registry.get(parent.name()) {
                parent_type
            } else {
                let &(parent_span, parent_parent) = map.get(&parent.name()).unwrap_or_else(|| {
                    let error = Error::UndefinedType(parent.name());
                    self.errors.push(parent.span().wrap(error));
                    &(builtins::SPAN, None)
                });
                self.define_class(map, parent.name(), parent_span, parent_parent)
            }
        });

        if let Some(ty) = self.registry.get(name) {
            return ty;
        }
        self.registry
            .define(name, span, parent.as_ref())
            .expect("impossible due to check above")
    }
}

type ClassDefinitionMap = HashMap<Interned<str>, (Span, Option<TypeName>)>;

pub enum Error {
    DuplicateTypeDefinition {
        name: Interned<str>,
        other_definition_span: Span,
    },
    UndefinedType(Interned<str>),
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use std::collections::HashMap;

    use crate::{ast::Program, parser, type_checker::Checker, util::intern::Interner};

    #[test]
    fn test_build_type_registry() {
        let (interner, prog) = parse_program(
            "
            class Entity {};
            class Mob inherits Entity {};
            class Cow inherits Mob {};
            class Block inherits Entity {};
            ",
        );
        let mut checker = Checker::with_capacity(16);
        checker.build_type_registry(&prog);
        assert!(checker.errors.is_empty());
        assert_eq!(
            checker.registry.hierarchy(&interner),
            HashMap::from([
                ("Cow", vec!["Cow", "Mob", "Entity", "Object", "<no-type>"]),
                ("Io", vec!["Io", "Object", "<no-type>"]),
                ("String", vec!["String", "Object", "<no-type>"]),
                ("Int", vec!["Int", "Object", "<no-type>"]),
                ("Bool", vec!["Bool", "Object", "<no-type>"]),
                ("Entity", vec!["Entity", "Object", "<no-type>"]),
                ("Object", vec!["Object", "<no-type>"]),
                ("Block", vec!["Block", "Entity", "Object", "<no-type>"]),
                ("<no-type>", vec!["<no-type>"]),
                ("Mob", vec!["Mob", "Entity", "Object", "<no-type>"]),
            ])
        );
    }

    fn parse_program(src: &str) -> (Interner<str>, Program) {
        let mut i = Interner::with_capacity(32);
        let prog = parser::parse_program(src, &mut Vec::with_capacity(512), &mut i)
            .expect("failed to parse");
        (i, prog)
    }
}
