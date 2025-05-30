use std::collections::HashMap;

use crate::{
    ast::{self, BinaryOperator, Expr, ExprKind, Program, TypeName, UnaryOperator},
    token::{Span, Spanned},
    types::{builtins, well_known, Type, TypeRegistry},
    util::intern::Interned,
};

pub type ParseResult<T> = Result<T, (T, Vec<Spanned<Error>>)>;

pub struct Checker {
    registry: TypeRegistry,
    methods: MethodsEnv,
    scopes: Vec<HashMap<Interned<str>, Type>>,
    current_class: Interned<str>,
    errors: Vec<Spanned<Error>>,
}

impl Checker {
    pub fn with_capacity(capacity: usize) -> Checker {
        Checker {
            registry: TypeRegistry::with_capacity(capacity),
            methods: HashMap::with_capacity(/* will be built in-place */ 0),
            scopes: Vec::with_capacity(24),
            current_class: builtins::NO_TYPE,
            errors: Vec::with_capacity(8),
        }
    }

    #[expect(clippy::type_complexity)]
    pub fn check(
        mut self,
        program: Program,
    ) -> Result<(Program<Type>, TypeRegistry), (Program<Type>, TypeRegistry, Vec<Spanned<Error>>)>
    {
        self.build_type_registry(&program);
        self.build_methods_env(&program);

        let classes = program
            .classes
            .into_iter()
            .map(|class| self.check_class(class))
            .collect();
        let program = Program { classes };

        if self.errors.is_empty() {
            Ok((program, self.registry))
        } else {
            Err((program, self.registry, self.errors))
        }
    }

    fn check_class(&mut self, class: ast::Class) -> ast::Class<Type> {
        self.current_class = class.name.name();
        let scope = self.get_class_scope(&class);
        let features = self.scoped(scope, move |this| {
            class
                .features
                .into_iter()
                .map(|feature| match feature {
                    ast::Feature::Attribute(binding) => {
                        ast::Feature::Attribute(this.check_binding(binding))
                    }
                    ast::Feature::Method(method) => ast::Feature::Method(this.check_method(method)),
                })
                .collect()
        });
        ast::Class {
            name: self.get_type(class.name),
            inherits: class.inherits,
            features,
        }
    }

    fn check_binding(&mut self, binding: ast::Binding) -> ast::Binding<Type> {
        let ty = self.get_type(binding.ty);
        let initializer = binding.initializer.map(|expr| self.check_expr(expr));
        ast::Binding {
            name: binding.name,
            ty,
            initializer,
        }
    }

    fn check_method(&mut self, method: ast::Method) -> ast::Method<Type> {
        let (formals, scope) = self.get_typed_formals_and_scope(method.formals);
        let body = self.scoped(scope, |this| this.check_expr(method.body));
        ast::Method {
            name: method.name,
            formals,
            return_ty: self.get_type(method.return_ty),
            body,
        }
    }

    #[expect(unused_variables)]
    fn check_expr(&mut self, expr: Expr) -> Expr<Type> {
        let (kind, ty) = match expr.kind {
            ExprKind::Assignment { target, value } => {
                let target_ty = self.lookup_scope(&target);
                let value = Box::new(self.check_expr(*value));
                let value_ty = value.ty.clone();
                self.assert_is_subtype(&value_ty, &target_ty, value.span);
                (ExprKind::Assignment { target, value }, value_ty)
            }
            ExprKind::Dispatch {
                qualifier,
                method,
                args,
            } => todo!(),
            ExprKind::Conditional {
                predicate,
                then_arm,
                else_arm,
            } => {
                let predicate = self.check_expr(*predicate);
                self.assert_is_type(&predicate.ty, builtins::BOOL, predicate.span);

                let then_arm = self.check_expr(*then_arm);
                let else_arm = self.check_expr(*else_arm);
                let lub = then_arm.ty.lub(&else_arm.ty);

                let kind = ExprKind::Conditional {
                    predicate: Box::new(predicate),
                    then_arm: Box::new(then_arm),
                    else_arm: Box::new(else_arm),
                };
                (kind, lub)
            }
            ExprKind::While { predicate, body } => {
                let predicate = Box::new(self.check_expr(*predicate));
                self.assert_is_type(&predicate.ty, builtins::BOOL, predicate.span);

                let body = Box::new(self.check_expr(*body));

                // Type of a while expression is Object (void)
                let object_ty = self.must_get_type(builtins::OBJECT);
                (ExprKind::While { predicate, body }, object_ty)
            }
            ExprKind::Block { body } => {
                let body: Vec<_> = body.into_iter().map(|e| self.check_expr(e)).collect();
                let last_ty = body
                    .last()
                    .expect("parser guarantees that sequence is never empty")
                    .ty
                    .clone();
                (ExprKind::Block { body }, last_ty)
            }
            ExprKind::Let { bindings, body } => {
                let (bindings, scope) = self.get_typed_bindings_and_scope(bindings);
                let body = self.scoped(scope, |this| this.check_expr(*body));
                let ty = body.ty.clone();
                let body = Box::new(body);
                (ExprKind::Let { bindings, body }, ty)
            }
            ExprKind::Case { predicate, arms } => {
                let mut lub = self.must_get_type(builtins::NO_TYPE);
                let predicate = Box::new(self.check_expr(*predicate));
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let ty = self.get_type(arm.ty);
                        let scope = Scope::from([(arm.name.name, ty.clone())]);
                        let body = self.scoped(scope, |this| this.check_expr(*arm.body));
                        lub = lub.lub(&body.ty);

                        ast::CaseArm {
                            name: arm.name,
                            ty,
                            body: Box::new(body),
                        }
                    })
                    .collect();
                (ExprKind::Case { predicate, arms }, lub)
            }
            ExprKind::New { ty } => {
                let ty = self.get_type_allowing_self_type(ty);
                (ExprKind::New { ty: ty.clone() }, ty)
            }
            ExprKind::Unary { op, expr } => {
                let unary = |this: &mut Checker, expr: Box<Expr<_>>, expected| {
                    let expr = Box::new(this.check_expr(*expr));
                    let ty = expr.ty.clone();
                    this.assert_is_type(&ty, expected, expr.span);
                    (ExprKind::Unary { op, expr }, ty)
                };

                match op {
                    UnaryOperator::IsVoid => {
                        let expr = Box::new(self.check_expr(*expr));
                        let ty = self.must_get_type(builtins::BOOL);
                        (ExprKind::Unary { op, expr }, ty)
                    }
                    UnaryOperator::Inverse => unary(self, expr, builtins::INT),
                    UnaryOperator::Not => unary(self, expr, builtins::BOOL),
                }
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let binary = |this: &mut Checker, expected, ret| {
                    let lhs = Box::new(this.check_expr(*lhs));
                    let rhs = Box::new(this.check_expr(*rhs));
                    this.assert_is_type(&lhs.ty, expected, lhs.span);
                    this.assert_is_type(&rhs.ty, expected, rhs.span);
                    (ExprKind::Binary { op, lhs, rhs }, this.must_get_type(ret))
                };

                match op {
                    BinaryOperator::Add => binary(self, builtins::INT, builtins::INT),
                    BinaryOperator::Sub => binary(self, builtins::INT, builtins::INT),
                    BinaryOperator::Mul => binary(self, builtins::INT, builtins::INT),
                    BinaryOperator::Div => binary(self, builtins::INT, builtins::INT),
                    BinaryOperator::Eq => todo!(),
                    BinaryOperator::Le => binary(self, builtins::INT, builtins::BOOL),
                    BinaryOperator::Leq => binary(self, builtins::INT, builtins::BOOL),
                }
            }
            ExprKind::Paren(expr) => {
                let expr = Box::new(self.check_expr(*expr));
                let ty = expr.ty.clone();
                (ExprKind::Paren(expr), ty)
            }
            ExprKind::Id(ident) => {
                let ty = self.lookup_scope(&ident);
                (ExprKind::Id(ident), ty)
            }
            ExprKind::Int(int) => (ExprKind::Int(int), self.must_get_type(builtins::INT)),
            ExprKind::String(string) => (
                ExprKind::String(string),
                self.must_get_type(builtins::STRING),
            ),
            ExprKind::Bool(bool) => (ExprKind::Bool(bool), self.must_get_type(builtins::BOOL)),
            ExprKind::Dummy => (ExprKind::Dummy, self.must_get_type(builtins::NO_TYPE)),
        };
        Expr {
            kind,
            ty,
            span: expr.span,
        }
    }

    fn build_methods_env(&mut self, program: &Program) {
        self.methods = program
            .classes
            .iter()
            .flat_map(|class| Self::get_class_methods(class).map(move |method| (class, method)))
            .map(|(class, method)| {
                let key = MethodKey {
                    class: self.get_type(class.name),
                    name: method.name.name,
                };
                let signature = ast::MethodSignature {
                    name: method.name,
                    formals: method
                        .formals
                        .iter()
                        .map(|f| ast::Formal {
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
            // calling `self.define_class()`). Otherwise, `Object`'s parent
            // would be `Some(Object)` instead of `None`. Not only that, such
            // an implicit built-in inheritance relationships wouldn't be
            // persisted in the `discovered` map, which is itself used in
            // `define_class()`.
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

    /// Returns the corresponding type that should be in the type registry.
    ///
    /// If type is not present, returns [`builtins::NO_TYPE`] and records an
    /// error at the provided span.
    fn get_type(&mut self, ty: TypeName) -> Type {
        self.registry.get(ty.name()).unwrap_or_else(|| {
            let error = if ty.name() == well_known::SELF_TYPE {
                Error::IllegalSelfType
            } else {
                Error::UndefinedType(ty.name())
            };
            self.errors.push(ty.span().wrap(error));
            self.registry.get(builtins::NO_TYPE).unwrap()
        })
    }

    /// Returns the corresponding type that should be in the type registry.
    ///
    /// This has the same behavior of [`Self::get_type`], but also allows the
    /// resolution of [`well_known::SELF_TYPE`] as the type of the current
    /// class.
    ///
    /// This is implemented in a separate function since the usage of
    /// `SELF_TYPE` is more restricted than the one of a "regular type". I.e.,
    /// `SELF_TYPE` is not allowed in all places in which a type can be used.
    fn get_type_allowing_self_type(&mut self, ty: TypeName) -> Type {
        if ty.name() == well_known::SELF_TYPE {
            self.get_current_class()
        } else {
            self.get_type(ty)
        }
    }

    /// Returns a type by its name, or panics.
    fn must_get_type(&self, ty: Interned<str>) -> Type {
        self.registry.get(ty).expect("got undefined type")
    }

    /// Returns the type of the current class.
    fn get_current_class(&self) -> Type {
        self.must_get_type(self.current_class)
    }

    /// Asserts that `a` is a subtype of `b`. If not, registers a new error
    /// (variant [`Error::Unassignable`]) with the provided span.
    fn assert_is_subtype(&mut self, a: &Type, b: &Type, span: Span) {
        if !a.is_subtype_of(b) {
            // This case is probably a consequence of a previous error, so we
            // don't emit another error if that's the case.
            if b.name() == builtins::NO_TYPE {
                // Just assumed that we have at least one error (which caused
                // this one).
                assert!(!self.errors.is_empty());
                return;
            }
            self.errors.push(span.wrap(Error::Unassignable {
                dst: b.name(),
                src: a.name(),
            }));
        }
    }

    /// Asserts that both types are equal.
    ///
    /// See also [`Self::assert_is_subtype`].
    fn assert_is_type(&mut self, actual: &Type, expected: Interned<str>, span: Span) {
        if actual.name() != expected {
            self.errors.push(span.wrap(Error::Mismatch {
                actual: actual.name(),
                expected,
            }));
        }
    }
}

// Utility functions
impl Checker {
    /// Looks up in the scope stack, or returns [`builtins::NO_TYPE`] with a
    /// registered error if not find.
    fn lookup_scope(&mut self, ident: &ast::Ident) -> Type {
        for scope in self.scopes.iter().rev() {
            if let Some(ty) = scope.get(&ident.name) {
                return ty.clone();
            }
        }
        let error = Error::UndefinedName(ident.name);
        self.errors.push(ident.span.wrap(error));
        self.must_get_type(builtins::NO_TYPE)
    }

    fn scoped<T>(&mut self, scope: Scope, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(scope);
        let res = f(self);
        self.scopes.pop();
        res
    }

    fn get_class_methods(class: &ast::Class) -> impl Iterator<Item = &ast::Method> + '_ {
        class.features.iter().filter_map(move |feature| {
            if let ast::Feature::Method(method) = feature {
                Some(method)
            } else {
                None
            }
        })
    }

    fn get_class_scope(&mut self, class: &ast::Class) -> Scope {
        // self : SELF_TYPE
        let current_class = self.get_current_class();

        class
            .features
            .iter()
            .filter_map(|feature| {
                if let ast::Feature::Attribute(binding) = feature {
                    Some((binding.name.name, self.get_type(binding.ty)))
                } else {
                    None
                }
            })
            .chain([(well_known::SELF, current_class)])
            .collect()
    }

    fn get_typed_formals_and_scope(
        &mut self,
        formals: Vec<ast::Formal>,
    ) -> (Vec<ast::Formal<Type>>, Scope) {
        let mut scope = Scope::with_capacity(formals.len());
        let formals = formals
            .into_iter()
            .map(|formal| {
                let ty = self.get_type(formal.ty);
                scope.insert(formal.name.name, ty.clone());
                ast::Formal {
                    name: formal.name,
                    ty,
                }
            })
            .collect();
        (formals, scope)
    }

    /// NOTE: Resolves bindings' types allowing for `SELF_TYPE`!
    fn get_typed_bindings_and_scope(
        &mut self,
        bindings: Vec<ast::Binding>,
    ) -> (Vec<ast::Binding<Type>>, Scope) {
        let mut scope = Scope::with_capacity(bindings.len());
        let bindings = bindings
            .into_iter()
            .map(|binding| {
                let ty = self.get_type_allowing_self_type(binding.ty);
                scope.insert(binding.name.name, ty.clone());
                ast::Binding {
                    name: binding.name,
                    initializer: binding.initializer.map(|i| {
                        let expr = self.check_expr(i);
                        self.assert_is_subtype(&expr.ty, &ty, expr.span);
                        expr
                    }),
                    ty,
                }
            })
            .collect();
        (bindings, scope)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Error {
    DuplicateTypeDefinition {
        name: Interned<str>,
        other_definition_span: Span,
    },
    UndefinedType(Interned<str>),
    UndefinedName(Interned<str>),
    Unassignable {
        dst: Interned<str>,
        src: Interned<str>,
    },
    Mismatch {
        actual: Interned<str>,
        expected: Interned<str>,
    },
    IllegalSelfType,
}

type DiscoveredClasses = HashMap<Interned<str>, (Span, Option<TypeName>)>;

type MethodsEnv = HashMap<MethodKey, ast::MethodSignature<Type>>;

type Scope = HashMap<Interned<str>, Type>;

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
        parser::test_utils::parse_program,
        token::Spanned,
        type_checker::{test_utils::typing_tests, Checker, Error, MethodsEnv},
        util::intern::Interner,
    };

    typing_tests!(
        fn test_int() {
            let expr = "1";
            let tree_ok = "int 1 (0..1 %: Int)";
        }

        fn test_true() {
            let expr = "true";
            let tree_ok = "bool true (0..4 %: Bool)";
        }

        fn test_false() {
            let expr = "false";
            let tree_ok = "bool false (0..5 %: Bool)";
        }

        fn test_string() {
            let expr = r#" "hello!" "#;
            let tree_ok = r#"string "hello!" (1..9 %: String)"#;
        }

        fn test_self() {
            let program = "
                class A {
                  a() : A { self };
                };
            ";
            let tree_ok = "
                class A
                  method a() : A
                    ident self (55..59 %: A)
            ";
        }

        fn test_let_ok() {
            let expr = "let a : Bool <- true in a";
            let tree_ok = "
                let (0..25 %: Bool)
                  binding a: Bool (initialized)
                    bool true (16..20 %: Bool)
                  in
                    ident a (24..25 %: Bool)
            ";
        }

        fn test_let_subtype_ok() {
            let expr = "let a : Object <- 1 in a";
            let tree_ok = "
                let (0..24 %: Object)
                  binding a: Object (initialized)
                    int 1 (18..19 %: Int)
                  in
                    ident a (23..24 %: Object)
            ";
        }

        fn test_let_ok_self_type() {
            let program = "
                class A {
                  a() : A { let a : SELF_TYPE <- self in a };
                };
            ";
            let tree_ok = "
                class A
                  method a() : A
                    let (55..85 %: A)
                      binding a: A (initialized)
                        ident self (76..80 %: A)
                      in
                        ident a (84..85 %: A)
            ";
        }

        fn test_let_error() {
            let expr = "let a : Bool <- 0 in a";
            let expected_errors = &["16..17: type Int is not assignable to type Bool"];
        }

        fn test_if_same_type() {
            let expr = "if true then 1 else 2 fi";
            let tree_ok = "
                conditional (0..24 %: Int)
                  bool true (3..7 %: Bool)
                  int 1 (13..14 %: Int)
                  int 2 (20..21 %: Int)
            ";
        }

        fn test_if_lub() {
            let expr = "if true then 1 else true fi";
            let tree_ok = "
                conditional (0..27 %: Object)
                  bool true (3..7 %: Bool)
                  int 1 (13..14 %: Int)
                  bool true (20..24 %: Bool)
            ";
        }

        fn test_if_fails_with_wrong_predicate_type() {
            let expr = "if 1 then false else false fi";
            let expected_errors = &["3..4: expected type Bool, but got Int"];
        }

        fn test_block_aka_sequence() {
            let expr = r#" { 1; true; "ok" } "#;
            let tree_ok = r#"
                block (1..18 %: String)
                  int 1 (3..4 %: Int)
                  bool true (6..10 %: Bool)
                  string "ok" (12..16 %: String)
            "#;
        }

        fn test_case() {
            let expr = "
                case 1 of
                    n : Int => n;
                    s : String => s;
                esac
            ";
            let tree_ok = "
                case (17..118 %: Object)
                  int 1 (22..23 %: Int)
                  arm n: Int =>
                    ident n (58..59 %: Int)
                  arm s: String =>
                    ident s (95..96 %: String)
            ";
        }

        fn test_assign_ok() {
            let expr = "let a : Int in a <- 1";
            let tree_ok = "
                let (0..21 %: Int)
                  binding a: Int
                  in
                    assignment a (15..21 %: Int)
                      int 1 (20..21 %: Int)
            ";
        }

        fn test_assign_ok_subtype() {
            let expr = "let a : Object in a <- 1";
            let tree_ok = "
                let (0..24 %: Int)
                  binding a: Object
                  in
                    assignment a (18..24 %: Int)
                      int 1 (23..24 %: Int)
            ";
        }

        fn test_assign_fails_with_undefined_name() {
            let expr = "a <- 1";
            let expected_errors = &["0..1: a is not defined"];
        }

        fn test_assign_fails_with_unassignable_type() {
            let expr = "let a : Int in a <- true";
            let expected_errors = &["20..24: type Bool is not assignable to type Int"];
        }

        fn test_while() {
            let expr = "while true loop 1 pool";
            let tree_ok = "
                while (0..22 %: Object)
                  bool true (6..10 %: Bool)
                  int 1 (16..17 %: Int)
            ";
        }

        fn test_while_fails_with_wrong_predicate_type() {
            let expr = "while 2 loop 1 pool";
            let expected_errors = &["6..7: expected type Bool, but got Int"];
        }

        fn test_binary_and_unary_ok() {
            let expr = "
                {
                    isvoid true;
                    isvoid 1;
                    !true;
                    ~1;
                    1 + 1;
                    1 - 1;
                    1 * 1;
                    1 / 1;
                    1 < 1;
                    1 <= 1;
                }
            ";
            let tree_ok = "
                block (17..313 %: Bool)
                  unary IsVoid (39..50 %: Bool)
                    bool true (46..50 %: Bool)
                  unary IsVoid (72..80 %: Bool)
                    int 1 (79..80 %: Int)
                  unary Not (102..107 %: Bool)
                    bool true (103..107 %: Bool)
                  unary Inverse (129..131 %: Int)
                    int 1 (130..131 %: Int)
                  binary Add (153..158 %: Int)
                    int 1 (153..154 %: Int)
                    int 1 (157..158 %: Int)
                  binary Sub (180..185 %: Int)
                    int 1 (180..181 %: Int)
                    int 1 (184..185 %: Int)
                  binary Mul (207..212 %: Int)
                    int 1 (207..208 %: Int)
                    int 1 (211..212 %: Int)
                  binary Div (234..239 %: Int)
                    int 1 (234..235 %: Int)
                    int 1 (238..239 %: Int)
                  binary Le (261..266 %: Bool)
                    int 1 (261..262 %: Int)
                    int 1 (265..266 %: Int)
                  binary Leq (288..294 %: Bool)
                    int 1 (288..289 %: Int)
                    int 1 (293..294 %: Int)
            ";
        }

        fn test_all_binary_operator_failures_in_block() {
            let expr = r#"
                {
                    !1;
                    ~true;
                    true + 1;
                    1 + true;
                    "a" + false;
                    false - 1;
                    1 - "str";
                    "s" * 1;
                    1 * true;
                    true / 1;
                    1 / "str";
                    true < 1;
                    1 < "str";
                    "a" < false;
                    false <= 1;
                    1 <= "s";
                }
             "#;
            let expected_errors = &[
                "40..41: expected type Bool, but got Int",
                "64..68: expected type Int, but got Bool",
                "90..94: expected type Int, but got Bool",
                "124..128: expected type Int, but got Bool",
                "150..153: expected type Int, but got String",
                "156..161: expected type Int, but got Bool",
                "183..188: expected type Int, but got Bool",
                "218..223: expected type Int, but got String",
                "245..248: expected type Int, but got String",
                "278..282: expected type Int, but got Bool",
                "304..308: expected type Int, but got Bool",
                "338..343: expected type Int, but got String",
                "365..369: expected type Int, but got Bool",
                "399..404: expected type Int, but got String",
                "426..429: expected type Int, but got String",
                "432..437: expected type Int, but got Bool",
                "459..464: expected type Int, but got Bool",
                "496..499: expected type Int, but got String",
            ];
        }

        fn test_new_ok() {
            let expr = "new String";

            let tree_ok = "new String (0..10 %: String)";
        }

        fn test_new_self_type_ok() {
            let program = "
                class A {
                  a() : A { new SELF_TYPE };
                };
            ";
            let tree_ok = "
                class A
                  method a() : A
                    new A (55..68 %: A)
            ";
        }
    );

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
                ("Cow", vec!["Cow", "Mob", "Entity", "Object"]),
                ("Io", vec!["Io", "Object"]),
                ("String", vec!["String", "Object"]),
                ("Int", vec!["Int", "Object"]),
                ("Bool", vec!["Bool", "Object"]),
                ("Entity", vec!["Entity", "Object"]),
                ("Object", vec!["Object"]),
                ("Block", vec!["Block", "Entity", "Object"]),
                ("<no-type>", vec!["<no-type>", "Object"]),
                ("Mob", vec!["Mob", "Entity", "Object"]),
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
        assert_errors(
            &i,
            &checker.errors,
            &[
                "48..54: Entity already defined at 19..25",
                "78..84: Object already defined at 0..0",
            ],
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
        assert_errors(
            &i,
            &checker.errors,
            &["35..49: class UndefinedClass is not defined"],
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
            fmt_methods(&i, &checker.methods),
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
        assert_errors(
            &i,
            &checker.errors,
            &[
                "64..74: class Undefined1 is not defined",
                "115..125: class Undefined2 is not defined",
                "163..173: class Undefined3 is not defined",
            ],
        );
    }

    fn assert_errors(i: &Interner<str>, actual: &[Spanned<Error>], expected: &[&str]) {
        let errors: Vec<_> = actual.iter().map(|e| fmt_error(i, e)).collect();
        assert_eq!(errors, expected);
    }

    fn fmt_error(i: &Interner<str>, error: &Spanned<Error>) -> String {
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
                format!("{span}: class {name} is not defined")
            }
            Error::UndefinedName(name) => {
                let name = i.get(name);
                format!("{span}: {name} is not defined")
            }
            Error::Unassignable { dst, src } => {
                let dst = i.get(dst);
                let src = i.get(src);
                format!("{span}: type {src} is not assignable to type {dst}")
            }
            Error::Mismatch { actual, expected } => {
                let actual = i.get(actual);
                let expected = i.get(expected);
                format!("{span}: expected type {expected}, but got {actual}")
            }
            Error::IllegalSelfType => format!("{span}: illegal use of SELF_TYPE"),
        }
    }

    fn fmt_methods<'i>(
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

#[cfg(test)]
pub mod test_utils {
    macro_rules! typing_tests {
        (
            $(
                fn $test_name:ident() {
                    let $kind:ident = $source:expr;
                    $($assertions_tt:tt)*
                }
            )*
        ) => {
            $(
                #[test]
                fn $test_name() {
                    let (interner, untyped_ast) = typing_tests!(@@get_ast($kind), $source);
                    let checker = crate::type_checker::Checker::with_capacity(32);
                    let check_result = typing_tests!(@@check($kind), checker, untyped_ast);
                    let (typed_ast, _registry, errors) = match check_result {
                        Ok((typed_ast, registry)) => (typed_ast, registry, vec![]),
                        Err((typed_ast, registry, errors)) => (typed_ast, registry, errors),
                    };

                    let typed_ast = typing_tests!(@@cast_ast($kind), typed_ast);
                    let ctx = &(interner, typed_ast, errors);
                    typing_tests!(
                        @@expand_assertions($kind),
                        ctx,
                        [$($assertions_tt)*]
                    );
                }
            )*
        };

        (@@expand_assertions($kind:ident), $ctx:expr, []) => {};
        (
            @@expand_assertions($kind:ident), $ctx:expr,
            [
                let $assertion:ident = $assertion_expected:expr;
                $($rest_assertions_tt:tt)*
            ]
        ) => {
            {
                typing_tests!(
                    @@assertion($kind, $assertion),
                    $ctx,
                    $assertion_expected
                );
            }
            typing_tests!(
                @@expand_assertions($kind),
                $ctx,
                [$($rest_assertions_tt)*]
            );
        };

        (@@assertion($kind:ident, expected_errors), $ctx:expr, $expected:expr) => {
            let expected: &[&str] = $expected;
            let (i, _typed_ast, actual_errors) = $ctx;
            let errors: Vec<_> = actual_errors.iter().map(|e| fmt_error(&i, e)).collect();
            ::pretty_assertions::assert_eq!(errors, expected);
        };
        (@@assertion($kind:ident, tree_ok), $ctx:expr, $expected:expr) => {
            let expected = ::indoc::indoc! { $expected }.trim();
            let (i, typed_ast, actual_errors) = $ctx;
            let tree_str = typing_tests!(@@print_ast($kind), i, typed_ast);
            assert_eq!(actual_errors.len(), 0);
            ::pretty_assertions::assert_eq!(tree_str.trim(), expected);
        };
        (@@assertion($kind:ident, tree_with_error), $ctx:expr, $expected:expr) => {
            let expected = ::indoc::indoc! { $expected }.trim();
            let (i, typed_ast, _actual_errors) = $ctx;
            let tree_str = typing_tests!(@@print_ast($kind), i, typed_ast);
            ::pretty_assertions::assert_eq!(tree_str.trim(), expected);
        };
        (@@assertion($kind:ident, $assertion:ident), $ctx:expr, $expected:expr) => {
            compile_error!(concat!(
                "assertion '",
                stringify!($assertion),
                "' is not implemented for kind '",
                stringify!($kind),
                "'",
            ));
        };

        (@@get_ast(expr), $source:expr) => {
            crate::parser::test_utils::parse_expr($source)
        };
        (@@get_ast(program), $source:expr) => {
            crate::parser::test_utils::parse_program($source)
        };
        (@@get_ast($kind:ident), $source:expr) => {
            compile_error!(concat!(
                "can only use mode 'expr' or 'program' as source input. got '",
                stringify!($kind),
                "' instead",
            ));
        };

        (@@check(expr), $checker:expr, $ast:expr) => {{
            let prog = crate::ast::test_utils::from_expr_to_main_program($ast);
            $checker.check(prog)
        }};
        (@@check(program), $checker:expr, $ast:expr) => {
            $checker.check($ast)
        };

        (@@cast_ast(expr), $ast:expr) => {
            crate::ast::test_utils::from_main_program_to_expr($ast)
        };
        (@@cast_ast(program), $ast:expr) => {
            $ast
        };

        (@@print_ast(expr), $interner:expr, $ast:expr) => {
            crate::util::fmt::print_expr_string($interner, $ast)
        };
        (@@print_ast(program), $interner:expr, $ast:expr) => {
            crate::util::fmt::print_program_string($interner, $ast)
        };
    }
    pub(crate) use typing_tests;
}
