use std::{collections::HashMap, rc::Rc};

use crate::{token::Span, util::intern::Interned};

pub struct TypeRegistry {
    map: HashMap<Interned<str>, Type>,
}

impl TypeRegistry {
    pub fn with_capacity(capacity: usize) -> TypeRegistry {
        TypeRegistry {
            map: HashMap::with_capacity(capacity),
        }
    }

    pub fn has(&self, name: Interned<str>) -> bool {
        self.map.contains_key(&name)
    }

    pub fn get(&self, name: Interned<str>) -> Option<Type> {
        self.map.get(&name).cloned()
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
        Ok(ty)
    }
}

#[derive(Clone)]
pub struct Type(Rc<TypeInner>);

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

struct TypeInner {
    name: Interned<str>,
    /// Type definition site
    span: Span,
    parent: Option<Type>,
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
