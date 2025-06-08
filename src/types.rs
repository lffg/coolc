use std::{collections::HashMap, hash::Hash, rc::Rc};

use crate::{token::Span, util::intern::Interned};

#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct TypeRegistry {
    map: HashMap<Interned<str>, Type>,
}

impl TypeRegistry {
    pub fn with_capacity(capacity: usize) -> TypeRegistry {
        TypeRegistry {
            map: HashMap::with_capacity(capacity),
        }
    }

    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    pub fn has(&self, name: Interned<str>) -> bool {
        self.map.contains_key(&name)
    }

    pub fn get(&self, name: Interned<str>) -> Option<Type> {
        self.map.get(&name).cloned()
    }

    #[cfg(test)]
    pub fn hierarchy<'i>(
        &self,
        interner: &'i crate::util::intern::Interner<str>,
    ) -> std::collections::BTreeMap<&'i str, Vec<&'i str>> {
        self.map
            .iter()
            .map(|(k, v)| {
                let k = interner.get(*k);
                let v = std::iter::from_fn({
                    let mut curr = Some(v);
                    move || {
                        let c = curr.as_ref()?;
                        let name = interner.get(c.name());
                        curr = c.parent();
                        Some(name)
                    }
                });
                (k, v.collect())
            })
            .collect()
    }

    /// Attempts to define the provided type.
    ///
    /// Fails if the type is already defined.
    pub fn define(
        &mut self,
        name: Interned<str>,
        span: Span,
        parent: Option<&Type>,
    ) -> Result<Type, ()> {
        if self.has(name) {
            return Err(());
        }
        let ty = Type(Rc::new(TypeInner {
            name,
            span,
            parent: parent.cloned(),
        }));
        self.map.insert(name, ty.clone());
        Ok(ty)
    }
}

#[derive(Clone, Debug)]
pub struct Type(Rc<TypeInner>);

/// See comment in `PartialEq` implementation for [`Type`].
impl Hash for Type {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.name.hash(state);
    }
}

/// Since each type can only be defined once (see invariant in
/// [`TypeRegistry::define`]), we can use the interned name as the predicate for
/// type equality.
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name()
    }
}

impl Eq for Type {}

impl Default for Type {
    fn default() -> Self {
        Type(Rc::new(TypeInner {
            name: builtins::NO_TYPE,
            span: builtins::SPAN,
            parent: None,
        }))
    }
}

impl Type {
    pub fn is_subtype_of(&self, other: &Self) -> bool {
        if self.name() == builtins::NO_TYPE {
            return true;
        };
        let mut curr = self;
        loop {
            if curr == other {
                return true;
            }
            match curr.parent() {
                Some(other) => curr = other,
                None => return false,
            }
        }
    }

    /// Returns the lowest upper-bound of the two types.
    ///
    /// ```none
    ///                             /--- mob --- cow
    ///             /--- entity ---+
    ///            /                \--- chest
    /// object ---+
    ///            \--- item
    ///
    /// lub(cow, cow) = cow
    /// lub(cow, mob) = mob
    /// lub(chest, cow) = entity
    /// lub(cow, item) = object
    /// ```
    ///
    /// Note that this algorithm is not optimal in terms of performance, but for
    /// now we prioritize clarity.
    #[must_use]
    pub fn lub(&self, other: &Self) -> Type {
        let mut curr = self;
        while !other.is_subtype_of(curr) {
            curr = curr
                .parent()
                .expect("all types are subtype of `<object>` (the top-type)");
        }
        curr.clone()
    }

    /// Checks whether the type is primitive, i.e., `String`, `Int`, or `Bool`.
    pub fn is_primitive(&self) -> bool {
        self.name() == builtins::STRING
            || self.name() == builtins::INT
            || self.name() == builtins::BOOL
    }

    pub fn name(&self) -> Interned<str> {
        self.0.name
    }

    pub fn span(&self) -> Span {
        self.0.span
    }

    pub fn parent(&self) -> Option<&Type> {
        self.0.parent.as_ref()
    }
}

impl From<Type> for Interned<str> {
    fn from(value: Type) -> Self {
        value.name()
    }
}

impl From<&Type> for Interned<str> {
    fn from(value: &Type) -> Self {
        value.name()
    }
}

#[derive(Debug)]
struct TypeInner {
    name: Interned<str>,
    /// Type definition site
    span: Span,
    parent: Option<Type>,
}

/// Built-in types, which are always implicitly interned **and** defined.
///
/// See also [`well_known`].
pub mod builtins {
    use crate::{
        ast::{self, Ident, TypeName, Untyped},
        token::Span,
        util::intern::{Interned, Interner},
    };

    pub const SPAN: Span = Span::new_of_length(0, 0);

    define_methods! {
        class OBJECT("Object", 1) inherits None {
            abort() : Object;
            type_name() : String;
            copy() : SELF_TYPE;
        };

        class NO_TYPE("<no-type>", 2) inherits OBJECT {};

        class STRING("String", 3) inherits OBJECT {
            length() : Int;
            concat(s: String) : String;
            substr(i: Int, l: Int) : String;
        };

        class INT("Int", 4) inherits OBJECT {};

        class BOOL("Bool", 5) inherits OBJECT {};

        class IO("IO", 6) inherits OBJECT {
            out_string(x: String) : SELF_TYPE;
            out_int(x: Int) : SELF_TYPE;
            in_string(): String;
            in_int(): Int;
            exit(status: Int) : "<no-type>";
        };
    }

    pub struct BuiltInClass {
        pub id: Interned<str>,
        pub inherits: Option<Interned<str>>,
        pub name: &'static str,
        methods: &'static [BuiltInMethod],
    }

    impl BuiltInClass {
        pub fn build_ast(&self, i: &mut Interner<str>) -> ast::Class<Untyped> {
            fn ident(i: &mut Interner<str>, s: &str) -> Ident {
                let name = i.intern(s);
                Ident { name, span: SPAN }
            }

            fn type_name(i: &mut Interner<str>, s: &str) -> TypeName {
                TypeName(ident(i, s))
            }

            ast::Class {
                name: TypeName::new(self.id, SPAN),
                inherits: self.inherits.map(|i| TypeName::new(i, SPAN)),
                features: self
                    .methods
                    .iter()
                    .map(|m| {
                        ast::Feature::Method(ast::Method {
                            name: ident(i, m.name),
                            formals: m
                                .args
                                .iter()
                                .map(|(name, ty)| ast::Formal {
                                    name: ident(i, name),
                                    ty: type_name(i, ty),
                                })
                                .collect(),
                            return_ty: type_name(i, m.ret),
                            body: ast::Expr {
                                kind: ast::ExprKind::Dummy,
                                span: SPAN,
                                info: (),
                            },
                        })
                    })
                    .collect(),
            }
        }
    }

    pub struct BuiltInMethod {
        name: &'static str,
        /// Slice of (NAME, TYPE) tuples
        args: &'static [(&'static str, &'static str)],
        ret: &'static str,
    }

    pub(super) const fn interned(n: u32) -> Interned<str> {
        Interned::unchecked_new(std::num::NonZeroU32::new(n).unwrap())
    }

    macro_rules! define_methods {
        (
            $(
                class
                    $builtin_ident:ident($class_name:expr, $interned_handle:expr)
                    inherits $inherited:ident
                {
                    $(
                        $method:ident ($($arg_name:ident : $arg_ty:ty),*) : $ret_ty:tt ;
                    )*
                };
            )*
        ) => {
            $(
                pub const $builtin_ident: Interned<str> =
                    crate::types::builtins::interned($interned_handle);
            )*

            pub const ALL: &[&BuiltInClass] = &[
                $(&crate::types::builtins::classes::$builtin_ident,)*
            ];

            pub mod classes {
                use super::*;

                $(
                    #[allow(non_upper_case_globals)]
                    pub static $builtin_ident: BuiltInClass = BuiltInClass {
                        id: crate::types::builtins::$builtin_ident,
                        inherits: define_methods!(@@inherits, $inherited),
                        name: $class_name,
                        methods: &[
                            $(
                                BuiltInMethod {
                                    name: stringify!($method),
                                    args: &[
                                        $((stringify!($arg_name), stringify!($arg_ty)),)*
                                    ],
                                    ret: define_methods!(@@ret_ty, $ret_ty),
                                },
                            )*
                        ],
                    };
                )*
            }
        };
        (@@inherits, None) => { None };
        (@@inherits, $name:ident) => {
            Some(crate::types::builtins::$name)
        };
        (@@ret_ty, $ret:ident) => { stringify!($ret) };
        (@@ret_ty, $ret:expr) => { $ret };
    }
    use define_methods;
}

/// Well known names, which are always implicitly interned.
///
/// See also [`builtins`].
pub mod well_known {
    use crate::util::intern::Interned;

    pub const MAIN: Interned<str> = super::builtins::interned(7);
    pub const MAIN_NAME: &str = "Main";

    pub const MAIN_METHOD: Interned<str> = super::builtins::interned(8);
    pub const MAIN_METHOD_NAME: &str = "main";

    pub const SELF: Interned<str> = super::builtins::interned(9);
    pub const SELF_NAME: &str = "self";

    pub const SELF_TYPE: Interned<str> = super::builtins::interned(10);
    pub const SELF_TYPE_NAME: &str = "SELF_TYPE";

    pub const ALL: &[(Interned<str>, &str)] = &[
        (MAIN, MAIN_NAME),
        (MAIN_METHOD, MAIN_METHOD_NAME),
        (SELF, SELF_NAME),
        (SELF_TYPE, SELF_TYPE_NAME),
    ];
}

#[cfg(test)]
mod tests {
    use crate::util::intern::Interner;

    use super::*;

    #[test]
    fn is_subtype_of() {
        //               /--- mob --- cow
        //    object ----+
        //               \--- block

        let i = &mut Interner::with_capacity(4);
        let reg = &mut TypeRegistry::with_capacity(4);

        let object = define(i, reg, "object", None);
        let no_type = define(i, reg, "<no-type>", Some(&object));
        let mob = define(i, reg, "mob", Some(&object));
        let cow = define(i, reg, "cow", Some(&mob));
        let block = define(i, reg, "block", Some(&object));

        assert!(no_type.is_subtype_of(&no_type));
        assert!(no_type.is_subtype_of(&object));
        assert!(no_type.is_subtype_of(&mob));
        assert!(no_type.is_subtype_of(&cow));
        assert!(no_type.is_subtype_of(&block));
        assert!(!object.is_subtype_of(&no_type));
        assert!(!mob.is_subtype_of(&no_type));
        assert!(!cow.is_subtype_of(&no_type));
        assert!(!block.is_subtype_of(&no_type));

        assert!(object.is_subtype_of(&object));
        assert!(!object.is_subtype_of(&mob));
        assert!(!object.is_subtype_of(&cow));
        assert!(!object.is_subtype_of(&block));

        assert!(mob.is_subtype_of(&object));
        assert!(mob.is_subtype_of(&mob));
        assert!(!mob.is_subtype_of(&cow));
        assert!(!mob.is_subtype_of(&block));

        assert!(cow.is_subtype_of(&object));
        assert!(cow.is_subtype_of(&mob));
        assert!(cow.is_subtype_of(&cow));
        assert!(!cow.is_subtype_of(&block));

        assert!(block.is_subtype_of(&object));
        assert!(!block.is_subtype_of(&mob));
        assert!(!block.is_subtype_of(&cow));
        assert!(block.is_subtype_of(&block));
    }

    #[test]
    fn lub() {
        //                             /--- mob --- cow
        //             /--- entity ---+
        //            /                \--- chest
        // object ---+
        //            \--- item

        let i = &mut Interner::with_capacity(8);
        let reg = &mut TypeRegistry::with_capacity(8);

        let object = define(i, reg, "object", None);
        let _no_type = define(i, reg, "<no-type>", Some(&object));
        let entity = define(i, reg, "entity", Some(&object));
        let mob = define(i, reg, "mob", Some(&entity));
        let cow = define(i, reg, "cow", Some(&mob));
        let chest = define(i, reg, "chest", Some(&entity));
        let item = define(i, reg, "item", Some(&object));

        assert_eq!(&cow.lub(&cow), &cow);
        assert_eq!(&object.lub(&object), &object);

        assert_eq!(&cow.lub(&item), &object);
        assert_eq!(&item.lub(&cow), &object);

        assert_eq!(&cow.lub(&entity), &entity);
        assert_eq!(&entity.lub(&cow), &entity);

        assert_eq!(&chest.lub(&mob), &entity);
        assert_eq!(&mob.lub(&chest), &entity);
    }

    fn define(
        i: &mut Interner<str>,
        reg: &mut TypeRegistry,
        name: &str,
        parent: Option<&Type>,
    ) -> Type {
        let name = i.intern(name);
        reg.define(name, Span::new_of_length(0, 0), parent).unwrap()
    }
}
