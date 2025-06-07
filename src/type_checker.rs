use std::{
    borrow::Cow,
    collections::{BTreeMap, HashMap, HashSet},
    rc::Rc,
};

use crate::{
    ast::{self, BinaryOperator, Expr, ExprKind, Program, TypeName, UnaryOperator},
    token::{Span, Spanned},
    types::{builtins, well_known, Type, TypeRegistry},
    util::intern::{Interned, Interner},
};

pub type ParseResult<T> = Result<T, (T, Vec<Spanned<Error>>)>;

pub struct Checker<'ident> {
    registry: TypeRegistry,
    /// O environment.
    scopes: Vec<Scope>,
    /// M environment is contained here.
    ///
    /// Here we keep a record of every method and attribute of each class.
    classes: ClassesEnv,
    /// C environment.
    current_class: Interned<str>,
    errors: Vec<Spanned<Error>>,
    ident_interner: &'ident mut Interner<str>,
}

impl Checker<'_> {
    pub fn with_capacity(ident_interner: &mut Interner<str>, capacity: usize) -> Checker<'_> {
        Checker {
            registry: TypeRegistry::with_capacity(capacity),
            classes: HashMap::with_capacity(0),
            scopes: Vec::with_capacity(24),
            current_class: builtins::NO_TYPE,
            errors: Vec::with_capacity(8),
            ident_interner,
        }
    }

    #[expect(clippy::type_complexity)]
    pub fn check(
        mut self,
        program: Program,
    ) -> Result<(Program<Type>, TypeRegistry), (Program<Type>, TypeRegistry, Vec<Spanned<Error>>)>
    {
        self.build_type_registry(&program);
        self.build_classes_env(&program);

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
        let scope = Rc::clone(&self.classes[&class.name.name()].attributes);
        let scope = Scope::Class(scope);
        let features = self.scoped(scope, move |this| {
            let self_scope = Scope::Unit(well_known::SELF, this.get_current_class());
            this.scoped(self_scope, |this| {
                class
                    .features
                    .into_iter()
                    .map(|feature| match feature {
                        ast::Feature::Attribute(binding) => {
                            ast::Feature::Attribute(this.check_binding(binding))
                        }
                        ast::Feature::Method(method) => {
                            ast::Feature::Method(this.check_method(method))
                        }
                    })
                    .collect()
            })
        });
        ast::Class {
            name: self.get_type(class.name),
            inherits: class.inherits,
            features,
        }
    }

    fn check_binding(&mut self, binding: ast::Binding) -> ast::Binding<Type> {
        let ty = self.get_type_allowing_self_type(binding.ty);
        let initializer = binding.initializer.map(|expr| {
            let expr = self.check_expr(expr);
            self.assert_is_subtype(&expr.ty, &ty, expr.span);
            expr
        });
        ast::Binding {
            name: binding.name,
            ty,
            initializer,
        }
    }

    fn check_method(&mut self, method: ast::Method) -> ast::Method<Type> {
        let (formals, scope) = self.get_typed_formals_and_scope(method.formals);
        let body = self.scoped(scope, |this| this.check_expr(method.body));
        let return_ty = self.get_type_allowing_self_type(method.return_ty);
        self.assert_is_subtype(&body.ty, &return_ty, body.span);
        ast::Method {
            name: method.name,
            formals,
            return_ty,
            body,
        }
    }

    fn check_expr(&mut self, expr: Expr) -> Expr<Type> {
        let (kind, ty) = match expr.kind {
            ExprKind::Assignment { target, value } => {
                if target.name == well_known::SELF {
                    let error = Error::IllegalAssignmentToSelf;
                    self.errors.push(target.span.wrap(error));
                }
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
            } => 'block: {
                let curr_class = self.get_current_class();

                // Fetch and check qualifier types
                let (receiver_ty, qualifier_ty, qualifier) = match qualifier {
                    Some(ast::DispatchQualifier {
                        expr,
                        static_qualifier: Some(static_qualifier),
                    }) => {
                        let expr = Box::new(self.check_expr(*expr));
                        let receiver_ty = expr.ty.clone();
                        let static_qualifier_ty = self.get_type(static_qualifier);
                        // In the case of a statically qualified call, we must
                        // also make sure that the receiver type is a subtype of
                        // the static qualifier type.
                        self.assert_is_subtype(&receiver_ty, &static_qualifier_ty, expr.span);
                        (
                            receiver_ty,
                            static_qualifier_ty.clone(),
                            Some(ast::DispatchQualifier {
                                expr,
                                static_qualifier: Some(static_qualifier_ty),
                            }),
                        )
                    }
                    Some(ast::DispatchQualifier {
                        expr,
                        static_qualifier: None,
                    }) => {
                        let expr = Box::new(self.check_expr(*expr));
                        (
                            expr.ty.clone(),
                            expr.ty.clone(),
                            Some(ast::DispatchQualifier {
                                expr,
                                static_qualifier: None,
                            }),
                        )
                    }
                    None => (curr_class.clone(), curr_class.clone(), None),
                };

                let maybe_sig = self
                    .classes
                    .get(&qualifier_ty.name())
                    .and_then(|class_methods| class_methods.methods.get(&method.name))
                    .map(Rc::clone);

                // If the signature is not defined, register an error.
                // But we also want to check the arguments for completeness.
                let Some(sig) = maybe_sig else {
                    let error = Error::UndefinedMethod {
                        class: qualifier_ty.name(),
                        method: method.name,
                    };
                    self.errors.push(method.span.wrap(error));

                    let dispatch = ExprKind::Dispatch {
                        qualifier,
                        method,
                        args: args.into_iter().map(|arg| self.check_expr(arg)).collect(),
                    };
                    break 'block (dispatch, self.must_get_type(builtins::NO_TYPE));
                };

                // Check arguments
                if sig.formals.len() != args.len() {
                    let error = Error::IncorrectNumberOfArguments {
                        actual: args.len(),
                        expected: sig.formals.len(),
                    };
                    self.errors.push(method.span.wrap(error));
                }
                let args = sig
                    .formals
                    .iter()
                    .zip(args)
                    .map(|(formal_param, arg)| {
                        let arg = self.check_expr(arg);
                        let formal_ty = self.get_type(formal_param.ty);
                        self.assert_is_subtype(&arg.ty, &formal_ty, arg.span);
                        arg
                    })
                    .collect();

                // Check return type
                let return_ty = if sig.return_ty.name() == well_known::SELF_TYPE {
                    receiver_ty
                } else {
                    self.get_type(sig.return_ty)
                };

                let dispatch = ExprKind::Dispatch {
                    qualifier,
                    method,
                    args,
                };
                (dispatch, return_ty)
            }
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
                if 1 < bindings.len() {
                    return self.check_expr(ast::desugar::multi_binding_let(
                        bindings, body, expr.span, &expr.ty,
                    ));
                }
                let (bindings, scope) = self.get_typed_bindings_and_scope(bindings);
                let body = self.scoped(scope, |this| this.check_expr(*body));
                let ty = body.ty.clone();
                let body = Box::new(body);
                (ExprKind::Let { bindings, body }, ty)
            }
            ExprKind::Case { predicate, arms } => {
                let mut seen = HashSet::with_capacity(arms.len());
                let mut lub = self.must_get_type(builtins::NO_TYPE);
                let predicate = Box::new(self.check_expr(*predicate));
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let ty = self.get_type(arm.ty);
                        if seen.contains(&ty.name()) {
                            let error = Error::DuplicateCaseArmDiscriminant { name: ty.name() };
                            self.errors.push(arm.ty.span().wrap(error));
                        }
                        seen.insert(ty.name());
                        let scope = Scope::Unit(arm.name.name, ty.clone());
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
                let binary =
                    |this: &mut Checker, expected, lhs: Box<Expr<_>>, rhs: Box<Expr<_>>, ret| {
                        let lhs = Box::new(this.check_expr(*lhs));
                        let rhs = Box::new(this.check_expr(*rhs));
                        this.assert_is_type(&lhs.ty, expected, lhs.span);
                        this.assert_is_type(&rhs.ty, expected, rhs.span);
                        (ExprKind::Binary { op, lhs, rhs }, this.must_get_type(ret))
                    };

                match op {
                    BinaryOperator::Add => binary(self, builtins::INT, lhs, rhs, builtins::INT),
                    BinaryOperator::Sub => binary(self, builtins::INT, lhs, rhs, builtins::INT),
                    BinaryOperator::Mul => binary(self, builtins::INT, lhs, rhs, builtins::INT),
                    BinaryOperator::Div => binary(self, builtins::INT, lhs, rhs, builtins::INT),
                    BinaryOperator::Le => binary(self, builtins::INT, lhs, rhs, builtins::BOOL),
                    BinaryOperator::Leq => binary(self, builtins::INT, lhs, rhs, builtins::BOOL),
                    // Eq is handled specially in that a String, Int, or a Bool
                    // can only be compared with another String, Int, or Bool
                    // (respectively), but other types (which are all custom
                    // classes) can be freely compared with other types.
                    BinaryOperator::Eq => {
                        let lhs = Box::new(self.check_expr(*lhs));
                        let rhs = Box::new(self.check_expr(*rhs));
                        if lhs.ty.is_primitive() || rhs.ty.is_primitive() {
                            self.assert_is_type(&rhs.ty, lhs.ty.name(), rhs.span);
                        }
                        let ret = self.must_get_type(builtins::BOOL);
                        (ExprKind::Binary { op, lhs, rhs }, ret)
                    }
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

    fn build_classes_env(&mut self, program: &Program) {
        let classes: BTreeMap<_, _> = {
            // We first create the environment with the builtins.
            // For now, they don't have any methods.
            let builtins = builtins::ALL.iter().map(|builtin| {
                let ast = builtin.build_ast(self.ident_interner);
                (builtin.id, Cow::Owned(ast))
            });
            let user_defined = program
                .classes
                .iter()
                .map(|class| (class.name.name(), Cow::Borrowed(class)));
            builtins.chain(user_defined).collect()
        };

        // `classes` should be of type `BTreeMap` to guarantee a stable order
        // in this loop.
        for class in classes.values() {
            let class_ty = self.get_type(class.name);
            self.define_class_env(
                &classes,
                &class_ty,
                &mut HashMap::with_capacity(16),
                &mut HashMap::with_capacity(16),
            );
        }
    }

    /// Define the methods map for a single class and all of its parents.
    fn define_class_env(
        &mut self,
        classes: &BTreeMap<Interned<str>, Cow<'_, ast::Class>>,
        class_ty: &Type,
        seen_attributes: &mut HashMap<Interned<str>, Span>,
        seen_methods: &mut HashMap<Interned<str>, Span>,
    ) {
        fn assert_unseen_in_class(
            c: &mut Checker,
            map: &mut HashMap<Interned<str>, Span>,
            ident: ast::Ident,
            error: impl Fn(Span) -> Error,
        ) {
            if let Some(&prev) = map.get(&ident.name) {
                c.errors.push(ident.span.wrap(error(prev)));
            } else {
                map.insert(ident.name, ident.span);
            }
        }

        seen_attributes.clear();
        seen_methods.clear();

        if self.classes.contains_key(&class_ty.name()) {
            return; // Already defined methods for this class.
        }

        let parent = if let Some(parent_ty) = class_ty.parent() {
            // If we have a parent, define its environment before the current
            // (child) class.
            self.define_class_env(classes, parent_ty, seen_attributes, seen_methods);
            ClassEnv::clone(&self.classes[&parent_ty.name()])
        } else {
            ClassEnv::default()
        };

        // This builder keeps track of whether any method or attribute is
        // inserted. If not, the built env will point out to the parent's one.
        let mut current = parent.builder();

        let env = 'block: {
            let Some(class) = classes.get(&class_ty.name()) else {
                // If the current class is not defined, we just return the
                // parent's class env. Notice that we couldn't `return` or fail
                // early here—otherwise, we would break the recursive chain.
                break 'block parent;
            };

            for feature in &class.features {
                match feature {
                    ast::Feature::Attribute(binding) => {
                        let name = binding.name.name;
                        // Make sure the attribute is not seen in this class
                        assert_unseen_in_class(self, seen_attributes, binding.name, |other| {
                            Error::DuplicateAttributeInClass { other }
                        });
                        // Make sure the attribute is not being redefined
                        if let Some(parent_attr) = parent.attributes.get(&name) {
                            let other = parent_attr.declaration_span;
                            let error = Error::IllegalAttributeOverride { other };
                            self.errors.push(binding.name.span.wrap(error));
                        }
                        let attr = ClassAttribute {
                            declaration_span: binding.name.span,
                            ty: self.get_type_allowing_self_type(binding.ty),
                            order: current.next_attribute_order(),
                        };
                        current.add_attribute(name, attr);
                    }
                    ast::Feature::Method(method) => {
                        let name = method.name.name;
                        assert_unseen_in_class(self, seen_attributes, method.name, |other| {
                            Error::DuplicateMethodInClass { other }
                        });
                        let mut sig = ClassMethodSignature {
                            formals: method.formals.clone(),
                            return_ty: method.return_ty,
                            order: current.next_method_order(),
                        };
                        if let Some(parent_sig) = parent.methods.get(&name) {
                            self.assert_is_compatible_signature(&sig, parent_sig, method.name.span);
                            // An inherited method should use the same order.
                            sig.order = parent_sig.order;
                        }
                        current.add_method(name, sig);
                    }
                }
            }
            current.build()
        };

        let old = self.classes.insert(class_ty.name(), env);
        assert!(old.is_none());
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
        for builtin in builtins::ALL {
            let parent = builtin
                .inherits
                .map(|name| TypeName::new(name, builtins::SPAN));
            discovered.insert(builtin.id, (builtins::SPAN, parent));
        }

        // Build the map from the source and report any duplicate type
        // definition error, if any.
        for class in &program.classes {
            let class_name = Interned::from(class.name);
            let current_span = class.name.span();

            if discovered.contains_key(&class_name) {
                let (other, _) = discovered[&class_name];
                let error = Error::DuplicateTypeDefinition {
                    name: class_name,
                    other,
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
            self.must_get_type(builtins::NO_TYPE)
        })
    }

    /// Returns the corresponding type that should be in the type registry.
    ///
    /// If the type is not present, returns [`builtins::NO_TYPE`]. Notice that,
    /// unlike [`Self::get_type`], this method does **NOT** registers any type
    /// errors if the type is not defined.
    ///
    /// Panics if provided type name is self type.
    fn get_type_no_error(&self, ty: TypeName) -> Type {
        assert_ne!(ty.name(), well_known::SELF_TYPE);
        self.registry
            .get(ty.name())
            .unwrap_or_else(|| self.must_get_type(builtins::NO_TYPE))
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
            // This case is probably a consequence of a previous error, so we
            // don't emit another error if that's the case.
            if actual.name() == builtins::NO_TYPE {
                // Just assumed that we have at least one error (which caused
                // this one).
                assert!(!self.errors.is_empty());
                return;
            }
            self.errors.push(span.wrap(Error::Mismatch {
                actual: actual.name(),
                expected,
            }));
        }
    }

    /// Assert that two [`MethodSignature`]s match. Two signatures match if they
    /// have the same number of formal parameters, and the same return type.
    ///
    /// Notice that no subtype relations are used here. The spec explicitly
    /// requires an "exact" match.
    ///
    /// On a mismatch, the corresponding type error is registered. Notice that,
    /// for error messages, the first method should be the scrutiny (the
    /// overriding class), and the second should be the parent—which is being
    /// overridden.
    pub fn assert_is_compatible_signature(
        &mut self,
        child_sig: &ClassMethodSignature,
        parent_sig: &ClassMethodSignature,
        current_method_name_span: Span,
    ) {
        let actual = child_sig;
        let expected = parent_sig;

        if actual.formals.len() != expected.formals.len() {
            let actual = actual.formals.len();
            let expected = expected.formals.len();
            let error = Error::OverriddenWithIncorrectNumberOfParameters { actual, expected };
            self.errors.push(current_method_name_span.wrap(error));
        }

        for (actual, expected) in actual.formals.iter().zip(&expected.formals) {
            let actual_ty = self.get_type_no_error(actual.ty);
            let expected_ty = self.get_type_no_error(expected.ty);
            if actual_ty != expected_ty {
                let error = Error::OverriddenWithIncorrectParameterTypes {
                    actual: actual_ty.name(),
                    expected: expected_ty.name(),
                };
                self.errors.push(actual.ty.span().wrap(error));
            }
        }

        // Here we compare return types by their untyped name (`TypeName`) since
        // we must consider two signatures returning `SELF_TYPE` as compatible.
        // By resolving types first and then comparing then, the signatures
        // wouldn't match since each `SELF_TYPE` would be resolved differently.
        let actual_ret = TypeName::name(&actual.return_ty);
        let expected_ret = TypeName::name(&expected.return_ty);
        if actual_ret != expected_ret {
            let error = Error::OverriddenWithIncorrectReturnType {
                actual: actual_ret,
                expected: expected_ret,
            };
            self.errors.push(actual.return_ty.span().wrap(error));
        }
    }
}

// Utility functions
impl Checker<'_> {
    /// Looks up in the scope stack, or returns [`builtins::NO_TYPE`] with a
    /// registered error if not find.
    fn lookup_scope(&mut self, ident: &ast::Ident) -> Type {
        for scope in self.scopes.iter().rev() {
            if let Some(ty) = scope.get(ident.name) {
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
        (formals, scope.build())
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
        (bindings, scope.build())
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Error {
    DuplicateTypeDefinition {
        name: Interned<str>,
        other: Span,
    },
    DuplicateMethodInClass {
        other: Span,
    },
    DuplicateAttributeInClass {
        other: Span,
    },
    IllegalAttributeOverride {
        other: Span,
    },
    DuplicateCaseArmDiscriminant {
        name: Interned<str>,
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
    IllegalAssignmentToSelf,
    MaximumNumberOfParametersExceeded {
        current: usize,
    },
    OverriddenWithIncorrectNumberOfParameters {
        actual: usize,
        expected: usize,
    },
    OverriddenWithIncorrectParameterTypes {
        actual: Interned<str>,
        expected: Interned<str>,
    },
    OverriddenWithIncorrectReturnType {
        actual: Interned<str>,
        expected: Interned<str>,
    },
    UndefinedMethod {
        class: Interned<str>,
        method: Interned<str>,
    },
    IncorrectNumberOfArguments {
        actual: usize,
        expected: usize,
    },
}

pub type DiscoveredClasses = HashMap<Interned<str>, (Span, Option<TypeName>)>;

/// Maps a class name to a map of methods and a map of attributes.
pub type ClassesEnv = HashMap<Interned<str>, ClassEnv>;

/// A class environment. We use a [`Rc`] to have copy-on-write semantics, such
/// that a child class has the same method map from its parent unless the former
/// defines a new method (which may even override some of the parent's methods).
#[derive(Clone, Default)]
pub struct ClassEnv {
    pub attributes: Rc<ClassAttributes>,
    pub methods: Rc<ClassMethods>,
}

impl ClassEnv {
    fn builder(&self) -> ClassEnvBuilder {
        ClassEnvBuilder {
            parent_attributes: Rc::clone(&self.attributes),
            parent_methods: Rc::clone(&self.methods),
            current_attributes: None,
            current_methods: None,
        }
    }
}

pub type ClassAttributes = HashMap<Interned<str>, Rc<ClassAttribute>>;
pub type ClassMethods = HashMap<Interned<str>, Rc<ClassMethodSignature>>;

pub struct ClassAttribute {
    pub declaration_span: Span,
    pub ty: Type,
    pub order: u32,
}

/// A method signature. Notice that formal parameters and the return use the
/// nominal [`TypeName`] since when dispatching method, one needs to
/// differentiate between an unresolved (nominal) `SELF_TYPE` and other types.
pub struct ClassMethodSignature {
    pub formals: Vec<ast::Formal<TypeName>>,
    pub return_ty: TypeName,
    pub order: u32,
}

struct ClassEnvBuilder {
    parent_attributes: Rc<ClassAttributes>,
    parent_methods: Rc<ClassMethods>,
    current_attributes: Option<ClassAttributes>,
    current_methods: Option<ClassMethods>,
}

impl ClassEnvBuilder {
    fn add_attribute(&mut self, name: Interned<str>, attribute: ClassAttribute) {
        self.current_attributes
            .get_or_insert_with(|| ClassAttributes::clone(&self.parent_attributes))
            .insert(name, Rc::new(attribute));
    }

    fn add_method(&mut self, name: Interned<str>, sig: ClassMethodSignature) {
        self.current_methods
            .get_or_insert_with(|| ClassMethods::clone(&self.parent_methods))
            .insert(name, Rc::new(sig));
    }

    fn next_attribute_order(&self) -> u32 {
        1 + u32::try_from(
            self.current_attributes
                .as_ref()
                .unwrap_or(&*self.parent_attributes)
                .len(),
        )
        .unwrap()
    }

    fn next_method_order(&self) -> u32 {
        1 + u32::try_from(
            self.current_methods
                .as_ref()
                .unwrap_or(&*self.parent_methods)
                .len(),
        )
        .unwrap()
    }

    fn build(self) -> ClassEnv {
        ClassEnv {
            attributes: self
                .current_attributes
                .map(Rc::new)
                .unwrap_or(self.parent_attributes),
            methods: self
                .current_methods
                .map(Rc::new)
                .unwrap_or(self.parent_methods),
        }
    }
}

enum Scope {
    Unit(Interned<str>, Type),
    Multi(Rc<HashMap<Interned<str>, Type>>),
    Class(Rc<ClassAttributes>),
    Null,
}

impl Scope {
    fn get(&self, key: Interned<str>) -> Option<&Type> {
        match self {
            Scope::Unit(name, ty) if *name == key => Some(ty),
            Scope::Unit(_, _) => None,
            Scope::Multi(map) => map.get(&key),
            Scope::Class(map) => map.get(&key).map(|attr| &attr.ty),
            Scope::Null => None,
        }
    }

    fn with_capacity(capacity: usize) -> ScopeBuilder {
        ScopeBuilder {
            map: HashMap::with_capacity(capacity),
        }
    }
}

struct ScopeBuilder {
    map: HashMap<Interned<str>, Type>,
}

impl ScopeBuilder {
    fn insert(&mut self, name: Interned<str>, ty: Type) -> Option<Type> {
        self.map.insert(name, ty)
    }

    fn build(self) -> Scope {
        match self.map.len() {
            0 => Scope::Null,
            1 => {
                let (name, ty) = self.map.into_iter().next().unwrap();
                Scope::Unit(name, ty)
            }
            _ => Scope::Multi(Rc::new(self.map)),
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;
    use std::collections::BTreeMap;

    use crate::{
        parser::test_utils::parse_program,
        type_checker::{Checker, ClassesEnv},
        util::{
            intern::Interner,
            test_utils::{assert_errors, tree_tests},
        },
    };

    tree_tests!(
        use checker;

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

        fn test_no_propagation_of_no_type_error() {
            let expr = "a + 1";
            let expected_errors = &["0..1: a is not defined"];
        }

        fn test_multi_binding_let_ok() {
            let expr = "
              let a : Int <- 1,
                  b : Int <- a + 1
              in
                a + b
            ";
            let tree_ok = "
                let (15..106 %: Int)
                  binding a: Int (initialized)
                    int 1 (30..31 %: Int)
                  in
                    let (15..106 %: Int)
                      binding b: Int (initialized)
                        binary Add (62..67 %: Int)
                          ident a (62..63 %: Int)
                          int 1 (66..67 %: Int)
                      in
                        binary Add (101..106 %: Int)
                          ident a (101..102 %: Int)
                          ident b (105..106 %: Int)
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

        fn test_case_ok() {
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

        fn test_case_fails_with_duplicate_discriminant() {
            let expr = "
                case 1 of
                    n : Int => n;
                    s : String => s;
                    n2 : Int => n2;
                esac
            ";
            let expected_errors = &["123..126: type Int already in use as arm discriminant"];
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

        fn test_assign_to_self_fails() {
            let program = "
                class Foo {
                    foo() : Foo { self <- new Foo };
                };
            ";
            let expected_errors = &["63..67: illegal self assignment"];
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

        fn test_eq_ok() {
            let program = r#"
                class A {};
                class B {};

                class Program {
                  main() : Object {{
                    1 = 2;
                    true = false;
                    "oi" = "tchau";
                    new A = new A;
                    new A = new B;
                  }};
                };
            "#;
            let tree_ok = r#"
                class A
                class B
                class Program
                  method main() : Object
                    block (125..313 %: Bool)
                      binary Eq (147..152 %: Bool)
                        int 1 (147..148 %: Int)
                        int 2 (151..152 %: Int)
                      binary Eq (174..186 %: Bool)
                        bool true (174..178 %: Bool)
                        bool false (181..186 %: Bool)
                      binary Eq (208..222 %: Bool)
                        string "oi" (208..212 %: String)
                        string "tchau" (215..222 %: String)
                      binary Eq (244..257 %: Bool)
                        new A (244..249 %: A)
                        new A (252..257 %: A)
                      binary Eq (279..292 %: Bool)
                        new A (279..284 %: A)
                        new B (287..292 %: B)
            "#;
        }

        fn test_eq_error() {
            let expr = r#"
                {
                  0 = false;
                  "a" = 97;
                  true = "verdadeiro";
                }
            "#;
            let expected_errors = &[
                "41..46: expected type Int, but got Bool",
                "72..74: expected type String, but got Int",
                "101..113: expected type Bool, but got String",
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

        fn test_method_scope_ok() {
            let program = "
                class A {
                    a(a1: String, a2: Bool) : Int { { self; a1; a2; 0; } };
                };
            ";
            let tree_ok = "
                class A
                  method a(a1: String, a2: Bool) : Int
                    block (79..99 %: Int)
                      ident self (81..85 %: A)
                      ident a1 (87..89 %: String)
                      ident a2 (91..93 %: Bool)
                      int 0 (95..96 %: Int)
            ";
        }

        fn test_method_override_compatible_ok() {
            let program = "
                class A {
                    foo(p: Int) : Bool { true };
                };
                class B inherits A {
                    foo(p: Int) : Bool { false };
                };
            ";
            let tree_ok = "
                class A
                  method foo(p: Int) : Bool
                    bool true (68..72 %: Bool)
                class B inherits A
                  method foo(p: Int) : Bool
                    bool false (173..178 %: Bool)
            ";
        }

        fn test_method_override_self_type_compatible_ok() {
            let program = "
                class A {
                    foo() : SELF_TYPE { self };
                };
                class B inherits A {
                    foo() : SELF_TYPE { self };
                };
            ";
            let tree_ok = "
                class A
                  method foo() : A
                    ident self (67..71 %: A)
                class B inherits A
                  method foo() : B
                    ident self (171..175 %: B)
            ";
        }

        fn test_fails_to_override_with_different_signature() {
            let program = "
                class A {
                    foo(p: Int) : Bool { true };
                };
                class B inherits A {
                    foo(p: String) : Bool { false };
                };
                class C inherits A {
                    foo() : Bool { false };
                };
                class D inherits A {
                    foo(p: Int) : Int { 0 };
                };
                class E inherits A {
                    foo(p: Int, q: Int) : Bool { true };
                };
                class F inherits A {
                    foo(p: String, q: Int) : Bool { true };
                };
            ";
            let expected_errors = &[
                // B
                "159..165: overriding method with incorrect parameter type: \
                    expected type Int, but got String",
                // C
                "261..264: overriding method of originally 1 parameters, but new definition has 0",
                // D
                "375..378: overriding method with incorrect return type: \
                    expected type Bool, but got Int",
                // E
                "462..465: overriding method of originally 1 parameters, but new definition has 2",
                // F
                "575..578: overriding method of originally 1 parameters, but new definition has 2",
                "582..588: overriding method with incorrect parameter type: \
                    expected type Int, but got String",
            ];
        }

        fn test_fails_when_using_undefined_parameter_or_return_types() {
            let program = "
                class A {
                    a(a1: Undefined1) : Int { 0 };
                    b(b1: Int) : Undefined2 { 0 };
                    c(c1: Undefined3) : Undefined4 { 0 };
                };
            ";
            let expected_errors = &[
                "53..63: class Undefined1 is not defined",
                "111..121: class Undefined2 is not defined",
                "155..165: class Undefined3 is not defined",
                "169..179: class Undefined4 is not defined",
            ];
        }

        fn test_can_use_self_type_in_return_type() {
            let program = "
                class A {
                    a1() : SELF_TYPE { new SELF_TYPE };
                    a2() : SELF_TYPE { self };
                };
            ";
            let tree_ok = "
                class A
                  method a1() : A
                    new A (66..79 %: A)
                  method a2() : A
                    ident self (122..126 %: A)
            ";
        }

        fn test_method_return_type_ok() {
            let program = "
                class A {};
                class B inherits A {};
                class C {
                    c1() : A { new B };
                    c2() : A { new A };
                };
            ";
            let tree_ok = "
                class A
                class B inherits A
                class C
                  method c1() : A
                    new B (125..130 %: B)
                  method c2() : A
                    new A (165..170 %: A)
            ";
        }

        fn test_method_return_type_fails() {
            let program = "
                class A {};
                class B inherits A {};
                class C {
                    c() : B { new A };
                };
            ";
            let expected_errors = &["124..129: type A is not assignable to type B"];
        }

        fn test_can_not_use_self_type_in_parameters() {
            let program = "
                class a {
                    a1(this: SELF_TYPE) : Int { 0 };
                };
            ";
            let expected_errors = &["56..65: illegal use of SELF_TYPE"];
        }

        fn test_multiple_declarations_of_same_name_errors() {
            let program = "
                class A {};
                class A {
                    attr : Int;
                    attr : Int;

                    method() : Int { 0 };
                    method() : Int { 1 };
                };
            ";
            let expected_errors = &[
                "51..52: class A already defined at 23..24",
                "107..111: attribute with same name already defined at 75..79",
                "182..188: method with same name already defined at 140..146",
            ];
        }

        fn test_fails_when_override_attribute() {
            let program = "
                class A {
                    name: String;
                };
                class B inherits A {
                    name: String;
                };
            ";
            let expected_errors = &["137..141: can't override attribute defined at 47..51"];
        }

        fn test_fails_to_inherit_class_with_undefined_name() {
            let program = "
                class A inherits Undefined {};
            ";
            let expected_errors = &["34..43: class Undefined is not defined"];
        }

        fn test_attribute_scope_ok() {
            // Operationally, accessing `b` in `b`'s initializer uses the
            // default value for that type (`0` in the case of `Int`s).
            let program = "
                class A {
                    a : Int <- 1;
                    b : Int <- a + b + c;
                    c : Int <- 3;
                    d : SELF_TYPE <- self;
                };
            ";
            let tree_ok = "
                class A
                  attribute a: Int (initialized)
                    int 1 (58..59 %: Int)
                  attribute b: Int (initialized)
                    binary Add (92..101 %: Int)
                      binary Add (92..97 %: Int)
                        ident a (92..93 %: Int)
                        ident b (96..97 %: Int)
                      ident c (100..101 %: Int)
                  attribute c: Int (initialized)
                    int 3 (134..135 %: Int)
                  attribute d: A (initialized)
                    ident self (174..178 %: A)
            ";
        }

        fn test_inherited_attribute_scope_ok() {
            let program = "
                class A {
                    a : Int <- 1;
                    b : Int <- a + b;
                };
                class B inherits A {
                    c : Int <- a + b + c;
                    d : Int <- c + d;
                };
            ";
            let tree_ok = "
                class A
                  attribute a: Int (initialized)
                    int 1 (58..59 %: Int)
                  attribute b: Int (initialized)
                    binary Add (92..97 %: Int)
                      ident a (92..93 %: Int)
                      ident b (96..97 %: Int)
                class B inherits A
                  attribute c: Int (initialized)
                    binary Add (186..195 %: Int)
                      binary Add (186..191 %: Int)
                        ident a (186..187 %: Int)
                        ident b (190..191 %: Int)
                      ident c (194..195 %: Int)
                  attribute d: Int (initialized)
                    binary Add (228..233 %: Int)
                      ident c (228..229 %: Int)
                      ident d (232..233 %: Int)
            ";
        }

        fn test_dispatch_ok() {
            let program = "
                class A {
                    a() : Int { 0 };
                };
                class B inherits A {};
                class C inherits A {
                    a() : Int { 1 };
                };

                class Main {
                    do(a: A) : A { a };
                    main() : Int {{
                        do(new B);
                        self.do(new A);
                        self@Main.do(do(new B));
                        (new A).a();
                        (new C)@A.a();
                    }};
                };
            ";
            let tree_ok = "
                class A
                  method a() : Int
                    int 0 (59..60 %: Int)
                class B inherits A
                class C inherits A
                  method a() : Int
                    int 1 (191..192 %: Int)
                class Main
                  method do(a: A) : A
                    ident a (280..281 %: A)
                  method main() : Int
                    block (319..542 %: Int)
                      dispatch do (345..354 %: A)
                        arguments
                          new B (348..353 %: B)
                      dispatch do (380..394 %: A)
                        receiver
                          ident self (380..384 %: Main)
                        arguments
                          new A (388..393 %: A)
                      dispatch do (420..443 %: A)
                        receiver @ Main
                          ident self (420..424 %: Main)
                        arguments
                          dispatch do (433..442 %: A)
                            arguments
                              new B (436..441 %: B)
                      dispatch a (469..480 %: Int)
                        receiver
                          paren (469..476 %: A)
                            new A (470..475 %: A)
                      dispatch a (506..519 %: Int)
                        receiver @ A
                          paren (506..513 %: C)
                            new C (507..512 %: C)
            ";
        }

        fn test_self_type_ret_ok() {
            let program = "
                class Builder {
                    build() : SELF_TYPE { self };
                };
                class AbstractFactory inherits Builder {};
                class Main {
                    main() : AbstractFactory {
                        (new AbstractFactory).build()
                    };
                };
            ";
            let tree_ok = "
                class Builder
                  method build() : Builder
                    ident self (75..79 %: Builder)
                class AbstractFactory inherits Builder
                class Main
                  method main() : AbstractFactory
                    dispatch build (261..290 %: AbstractFactory)
                      receiver
                        paren (261..282 %: AbstractFactory)
                          new AbstractFactory (262..281 %: AbstractFactory)
            ";
        }

        fn test_dispatch_errors() {
            let program = "
                class A {
                    common(): Int { 0 };
                    a(): Int { 1 };
                };
                class B inherits A {
                    common(): Int { 2 };
                    b(): Int { 3 };
                };
                class Main {
                    main(a: A, b: B): Int {{
                        main(a, b, a); -- (1) more args
                        main(a, a); -- (2) incorrect (A instead of B in 2nd)
                        main(); -- (3) less args

                        a@B.b(); -- (4) A is not subtype of B

                        undefined1(); -- (5)
                        a.undefined2(); -- (6)
                        b@A.undefined3(); -- (7)

                        0;
                    }};
                };
            ";
            let expected_errors = &[
                // 1
                "354..358: incorrect number of arguments. expected 2, but got 3",
                // 2
                "418..419: type A is not assignable to type B",
                // 3
                "487..491: incorrect number of arguments. expected 2, but got 0",
                // 4
                "537..538: type A is not assignable to type B",
                // 5, 6, 7
                "600..610: undefined method undefined1 on class Main",
                "647..657: undefined method undefined2 on class A",
                "696..706: undefined method undefined3 on class A",
            ];
        }
    );

    #[test]
    fn test_build_type_registry() {
        let (mut i, prog) = parse_program(
            "
            class Entity {};
            class Mob inherits Entity {};
            class Cow inherits Mob {};
            class Block inherits Entity {};
            ",
        );
        let mut checker = Checker::with_capacity(&mut i, 16);
        checker.build_type_registry(&prog);
        assert!(checker.errors.is_empty());
        assert_eq!(
            checker.registry.hierarchy(&i),
            BTreeMap::from([
                ("Cow", vec!["Cow", "Mob", "Entity", "Object"]),
                ("IO", vec!["IO", "Object"]),
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
        let (mut i, prog) = parse_program(
            "
            class Entity {};
            class Entity {};

            class Object {};
            ",
        );
        let mut checker = Checker::with_capacity(&mut i, 16);
        checker.build_type_registry(&prog);
        assert_errors(
            checker.ident_interner,
            &checker.errors,
            &[
                "48..54: class Entity already defined at 19..25",
                "78..84: class Object already defined at 0..0",
            ],
        );
    }

    #[test]
    fn test_build_type_registry_fails_with_undefined_type() {
        let (mut i, prog) = parse_program(
            "
            class Entity inherits UndefinedClass {};
            ",
        );
        let mut checker = Checker::with_capacity(&mut i, 16);
        checker.build_type_registry(&prog);
        assert_errors(
            checker.ident_interner,
            &checker.errors,
            &["35..49: class UndefinedClass is not defined"],
        );
    }

    #[test]
    fn test_build_methods_env() {
        let (mut i, prog) = parse_program(
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
        let mut checker = Checker::with_capacity(&mut i, 16);
        checker.build_type_registry(&prog);
        checker.build_classes_env(&prog);
        assert!(checker.errors.is_empty());
        assert_eq!(
            fmt_methods(checker.ident_interner, &checker.classes),
            BTreeMap::from([
                (
                    ("A", "a1"),
                    vec![("a1p1", "String"), ("a1p2", "String"), ("<ret>", "Int")]
                ),
                (("A", "a2"), vec![("a2p1", "String"), ("<ret>", "Int")]),
                (("A", "a3"), vec![("<ret>", "Int")]),
                (("A", "a4"), vec![("<ret>", "Int")]),
                (("B", "b1"), vec![("<ret>", "Int")]),
                (
                    ("IO", "exit"),
                    vec![("status", "Int"), ("<ret>", "<no-type>")]
                ),
                (("IO", "in_int"), vec![("<ret>", "Int")]),
                (("IO", "in_string"), vec![("<ret>", "String")]),
                (
                    ("IO", "out_int"),
                    vec![("x", "Int"), ("<ret>", "SELF_TYPE")]
                ),
                (
                    ("IO", "out_string"),
                    vec![("x", "String"), ("<ret>", "SELF_TYPE")]
                ),
                (
                    ("String", "concat"),
                    vec![("s", "String"), ("<ret>", "String")]
                ),
                (("String", "length"), vec![("<ret>", "Int")]),
                (
                    ("String", "substr"),
                    vec![("i", "Int"), ("l", "Int"), ("<ret>", "String")]
                ),
            ])
        );
    }

    #[test]
    fn test_build_methods_env_considering_inheritance() {
        let (mut i, prog) = parse_program(
            "
            class A {
                a1(a: String) : Int { 0 };
            };
            class B inherits A {
                b1() : Int { 0 };
            };
            class C inherits A {};
            class D inherits C {
                a1(a: String) : Int { 1 };
                d1(d: Int) : Int { 2 };
            };
            ",
        );
        let mut checker = Checker::with_capacity(&mut i, 16);
        checker.build_type_registry(&prog);
        checker.build_classes_env(&prog);
        assert!(checker.errors.is_empty());
        assert_eq!(
            fmt_methods(checker.ident_interner, &checker.classes),
            BTreeMap::from([
                (("A", "a1"), vec![("a", "String"), ("<ret>", "Int")]),
                (("B", "a1"), vec![("a", "String"), ("<ret>", "Int")]),
                (("B", "b1"), vec![("<ret>", "Int")]),
                (("C", "a1"), vec![("a", "String"), ("<ret>", "Int")]),
                (("D", "a1"), vec![("a", "String"), ("<ret>", "Int")]),
                (("D", "d1"), vec![("d", "Int"), ("<ret>", "Int")]),
                (
                    ("IO", "exit"),
                    vec![("status", "Int"), ("<ret>", "<no-type>")]
                ),
                (("IO", "in_int"), vec![("<ret>", "Int")]),
                (("IO", "in_string"), vec![("<ret>", "String")]),
                (
                    ("IO", "out_int"),
                    vec![("x", "Int"), ("<ret>", "SELF_TYPE")]
                ),
                (
                    ("IO", "out_string"),
                    vec![("x", "String"), ("<ret>", "SELF_TYPE")]
                ),
                (
                    ("String", "concat"),
                    vec![("s", "String"), ("<ret>", "String")]
                ),
                (("String", "length"), vec![("<ret>", "Int")]),
                (
                    ("String", "substr"),
                    vec![("i", "Int"), ("l", "Int"), ("<ret>", "String")]
                ),
            ])
        );
    }

    fn fmt_methods<'i>(
        i: &'i Interner<str>,
        methods: &ClassesEnv,
    ) -> BTreeMap<(&'i str, &'i str), Vec<(&'i str, &'i str)>> {
        methods
            .iter()
            .flat_map(|(class_name, class_env)| {
                class_env
                    .methods
                    .iter()
                    .filter_map(move |(method_name, sig)| {
                        let name = i.get(method_name);
                        if name == "abort" || name == "type_name" || name == "copy" {
                            return None;
                        }
                        let k = (i.get(class_name), name);
                        let v = sig
                            .formals
                            .iter()
                            .map(|f| (i.get(f.name), i.get(f.ty.name())))
                            .chain([("<ret>", i.get(sig.return_ty.name()))])
                            .collect();
                        Some((k, v))
                    })
            })
            .collect()
    }
}
