use std::collections::HashMap;

use crate::{
    ast::{Feature, Formal, MethodSignature, Program, TypeName},
    token::{Span, Spanned},
    types::{builtins, Type, TypeRegistry},
    util::intern::Interned,
};

pub type ParseResult<T> = Result<T, (T, Vec<Spanned<Error>>)>;

pub struct Checker {
    registry: TypeRegistry,
    methods: MethodsEnv,
    errors: Vec<Spanned<Error>>,
}

impl Checker {
    pub fn with_capacity(capacity: usize) -> Checker {
        Checker {
            registry: TypeRegistry::with_capacity(capacity),
            methods: HashMap::with_capacity(/* will be built in-place */ 0),
            errors: Vec::with_capacity(8),
        }
    }

    /// Returns the corresponding type that should be in the type registry.
    ///
    /// If type is not present, returns [`builtins::NO_TYPE`] and records an
    /// error at the provided span.
    pub fn get_type(&mut self, ty: TypeName) -> Type {
        self.registry.get(ty.name()).unwrap_or_else(|| {
            self.errors
                .push(ty.span().wrap(Error::UndefinedType(ty.name())));
            self.registry.get(builtins::NO_TYPE).unwrap()
        })
    }

    pub fn check(mut self, program: Program) -> (Program<Type>, TypeRegistry) {
        self.build_type_registry(&program);
        self.build_methods_env(&program);

        (Program::default(), self.registry)
    }

    pub fn build_methods_env(&mut self, program: &Program) {
        self.methods = program
            .classes
            .iter()
            .flat_map(|class| {
                class.features.iter().filter_map(move |feature| {
                    if let Feature::Method(method) = feature {
                        Some((class, method))
                    } else {
                        None
                    }
                })
            })
            .map(|(class, method)| {
                let key = MethodKey {
                    class: self.get_type(class.name),
                    name: method.name.name,
                };
                let signature = MethodSignature {
                    name: method.name,
                    formals: method
                        .formals
                        .iter()
                        .map(|f| Formal {
                            name: f.name,
                            ty: self.get_type(f.ty),
                        })
                        .collect(),
                    return_ty: self.get_type(method.return_ty),
                };
                (key, signature)
            })
            .collect();
    }

    /// Scans through the program's source and records all classes in the
    /// `registry` field.
    fn build_type_registry(&mut self, program: &Program) {
        const OBJECT: TypeName = TypeName::new(builtins::OBJECT, builtins::SPAN);

        // Maps a class name to its definition span and parent class, if any.
        let mut discovered = DiscoveredClasses::with_capacity(self.registry.capacity());

        // Define built-ins.
        //
        // This will also help preventing built-in redefinition due to the
        // check in the next section.
        for &(ty, _, parent) in builtins::ALL {
            let parent = parent.map(|name| TypeName::new(name, builtins::SPAN));
            discovered.insert(ty, (builtins::SPAN, parent));
        }

        // Build the map from the source and report any duplicate type
        // definition error, if any.
        for class in &program.classes {
            let class_name = Interned::from(class.name);
            let current_span = class.name.span();

            if discovered.contains_key(&class_name) {
                let (other_span, _) = discovered[&class_name];
                let error = Error::DuplicateTypeDefinition {
                    name: class_name,
                    other_definition_span: other_span,
                };
                self.errors.push(current_span.wrap(error));
                continue;
            }

            // If the source doesn't define a parent class, object is implied.
            //
            // Notice that we do NOT want to make this default below (when
            // calling `self.define_class()`). Otherwise, `<no-type>`'s parent
            // would be `Some(Object)` instead of `None` and such implicit
            // built-in inheritance relationships wouldn't be persisted in the
            // `discovered` map, which is itself used in `define_class()`.
            // Yes, this was an excruciating bug.
            let val = (current_span, Some(class.inherits.unwrap_or(OBJECT)));
            discovered.insert(class.name.into(), val);
        }

        // Build up the type registry by recursively traversing discovered
        // declarations and their inheritance relationships.
        for (&class_name, &(class_span, parent)) in &discovered {
            self.define_class(&discovered, class_name, class_span, parent);
        }
    }

    fn define_class(
        &mut self,
        map: &DiscoveredClasses,
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

#[derive(Copy, Clone, Debug)]
pub enum Error {
    DuplicateTypeDefinition {
        name: Interned<str>,
        other_definition_span: Span,
    },
    UndefinedType(Interned<str>),
}

type DiscoveredClasses = HashMap<Interned<str>, (Span, Option<TypeName>)>;

type MethodsEnv = HashMap<MethodKey, MethodSignature<Type>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MethodKey {
    /// Class in which the method is defined.
    pub class: Type,
    /// Method name.
    pub name: Interned<str>,
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use std::collections::BTreeMap;

    use crate::{
        ast::Program,
        parser,
        token::Spanned,
        type_checker::{Checker, Error, MethodsEnv},
        util::intern::Interner,
    };

    #[test]
    fn test_build_type_registry() {
        let (i, prog) = parse_program(
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
            checker.registry.hierarchy(&i),
            BTreeMap::from([
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

    #[test]
    fn test_build_type_registry_fails_with_duplicate_class() {
        let (i, prog) = parse_program(
            "
            class Entity {};
            class Entity {};

            class Object {};
            ",
        );
        let mut checker = Checker::with_capacity(16);
        checker.build_type_registry(&prog);
        assert_eq!(checker.errors.len(), 2);
        assert_eq!(
            pp(&i, &checker.errors[0]),
            "48..54: Entity already defined at 19..25"
        );
        assert_eq!(
            pp(&i, &checker.errors[1]),
            "78..84: Object already defined at 0..0"
        );
    }

    #[test]
    fn test_build_type_registry_fails_with_undefined_type() {
        let (i, prog) = parse_program(
            "
            class Entity inherits UndefinedClass {};
            ",
        );
        let mut checker = Checker::with_capacity(16);
        checker.build_type_registry(&prog);
        assert_eq!(checker.errors.len(), 1);
        assert_eq!(
            pp(&i, &checker.errors[0]),
            "35..49: UndefinedClass is not defined"
        );
    }

    #[test]
    fn test_build_methods_env() {
        let (i, prog) = parse_program(
            "
            class A {
                a1(a1p1 : String, a1p2 : String) : Int { 0 };
                a2(a2p1 : String) : Int { 0 };
                a3() : Int { 0 };
                a4() : Int { 0 };
            };
            class B {
                b1() : Int { 0 };
            };
            ",
        );
        let mut checker = Checker::with_capacity(16);
        checker.build_type_registry(&prog);
        checker.build_methods_env(&prog);
        assert!(checker.errors.is_empty());
        assert_eq!(
            pp_methods(&i, &checker.methods),
            BTreeMap::from([
                (
                    ("A", "a1"),
                    vec![("a1p1", "String"), ("a1p2", "String"), ("<ret>", "Int")],
                ),
                (("A", "a2"), vec![("a2p1", "String"), ("<ret>", "Int")]),
                (("A", "a3"), vec![("<ret>", "Int")]),
                (("A", "a4"), vec![("<ret>", "Int")]),
                (("B", "b1"), vec![("<ret>", "Int")]),
            ])
        );
    }

    #[test]
    fn test_build_methods_env_fails_upon_undefined_types() {
        let (i, prog) = parse_program(
            "
            class A {
                a1(a1p1 : String, a1p2 : Undefined1) : Int { 0 };
                a2(a2p1 : Undefined2) : Int { 0 };
                a3() : Undefined3 { 0 };
            };
            ",
        );
        let mut checker = Checker::with_capacity(16);
        checker.build_type_registry(&prog);
        checker.build_methods_env(&prog);
        assert_eq!(checker.errors.len(), 3);
        assert_eq!(
            pp(&i, &checker.errors[0]),
            "64..74: Undefined1 is not defined"
        );
        assert_eq!(
            pp(&i, &checker.errors[1]),
            "115..125: Undefined2 is not defined"
        );
        assert_eq!(
            pp(&i, &checker.errors[2]),
            "163..173: Undefined3 is not defined"
        );
    }

    fn parse_program(src: &str) -> (Interner<str>, Program) {
        let mut i = Interner::with_capacity(32);
        let prog = parser::parse_program(src, &mut Vec::with_capacity(512), &mut i)
            .expect("failed to parse");
        (i, prog)
    }

    fn pp(i: &Interner<str>, error: &Spanned<Error>) -> String {
        let span = error.span;
        match error.inner {
            Error::DuplicateTypeDefinition {
                name,
                other_definition_span,
            } => {
                let name = i.get(name);
                format!("{span}: {name} already defined at {other_definition_span}")
            }
            Error::UndefinedType(name) => {
                let name = i.get(name);
                format!("{span}: {name} is not defined")
            }
        }
    }

    fn pp_methods<'i>(
        i: &'i Interner<str>,
        methods: &MethodsEnv,
    ) -> BTreeMap<(&'i str, &'i str), Vec<(&'i str, &'i str)>> {
        methods
            .iter()
            .map(|(k, v)| {
                let k = (i.get(k.class.name()), i.get(k.name));
                let v = v
                    .formals
                    .iter()
                    .map(|f| (i.get(f.name), i.get(f.ty.name())))
                    .chain([("<ret>", i.get(v.return_ty.name()))])
                    .collect();
                (k, v)
            })
            .collect()
    }
}
