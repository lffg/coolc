use std::{collections::HashMap, rc::Rc};

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
    ) -> HashMap<&'i str, Vec<&'i str>> {
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

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        self.name() == other.name()
    }
}

impl Type {
    pub fn is_subtype_of(&self, other: &Self) -> bool {
        let mut curr = self;
        loop {
            // Since each type can only be defined once (see invariant in
            // `TypeRegistry::define`), we can use the interned name as the
            // predicate for type equality.
            if curr.name() == other.name() {
                return true;
            }
            match curr.parent() {
                Some(other) => curr = other,
                None => return false,
            }
        }
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

#[derive(Debug)]
struct TypeInner {
    name: Interned<str>,
    /// Type definition site
    span: Span,
    parent: Option<Type>,
}

pub mod builtins {

    use crate::{token::Span, util::intern::Interned};

    pub const SPAN: Span = Span::new_of_length(0, 0);

    pub const NO_TYPE: Interned<str> = interned(1);
    pub const NO_TYPE_NAME: &str = "<no-type>";

    pub const OBJECT: Interned<str> = interned(2);
    pub const OBJECT_NAME: &str = "Object";

    pub const STRING: Interned<str> = interned(3);
    pub const STRING_NAME: &str = "String";

    pub const INT: Interned<str> = interned(4);
    pub const INT_NAME: &str = "Int";

    pub const BOOL: Interned<str> = interned(5);
    pub const BOOL_NAME: &str = "Bool";

    pub const IO: Interned<str> = interned(6);
    pub const IO_NAME: &str = "Io";

    #[allow(clippy::type_complexity)]
    pub const ALL: &[(Interned<str>, &str, Option<Interned<str>>)] = &[
        (NO_TYPE, NO_TYPE_NAME, None),
        (OBJECT, OBJECT_NAME, Some(NO_TYPE)),
        (STRING, STRING_NAME, Some(OBJECT)),
        (INT, INT_NAME, Some(OBJECT)),
        (BOOL, BOOL_NAME, Some(OBJECT)),
        (IO, IO_NAME, Some(OBJECT)),
    ];

    const fn interned(n: u32) -> Interned<str> {
        Interned::unchecked_new(std::num::NonZeroU32::new(n).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use crate::util::intern::Interner;

    use super::*;

    #[test]
    fn is_subtype_of() {
        //               /---- mob ---- cow
        //    object ----+
        //               \---- block

        let i = &mut Interner::with_capacity(4);
        let reg = &mut TypeRegistry::with_capacity(4);

        let object = define(i, reg, "object", None);
        let mob = define(i, reg, "mob", Some(&object));
        let cow = define(i, reg, "cow", Some(&mob));
        let block = define(i, reg, "block", Some(&object));

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
