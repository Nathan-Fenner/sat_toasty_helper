use std::{
    any::{Any, TypeId},
    collections::{BTreeMap, BTreeSet},
    sync::{Arc, Mutex},
};

/// A `Var` is an opaque identifier used for variables.
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Debug)]
pub struct Var(pub i32);

// A `Lit` is a positive or negative variable.
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Debug)]
pub enum Lit<Item: InternalProp> {
    Pos(Item),
    Neg(Item),
}

impl Lit<Var> {
    /// Returns the dimacs value (positive/negative integer).
    pub fn dimacs_int(self) -> i32 {
        match self {
            Self::Pos(v) => v.0,
            Self::Neg(v) => -v.0,
        }
    }
}

impl<A: InternalProp> Lit<A> {
    /// Maps the function `f` over literal `self`, preserving `Pos`/`Neg`.
    pub fn map<B: InternalProp>(self, f: impl FnOnce(A) -> B) -> Lit<B> {
        match self {
            Lit::Pos(v) => Lit::Pos(f(v)),
            Lit::Neg(v) => Lit::Neg(f(v)),
        }
    }

    /// Negates the literal, replacing `Pos` with `Neg` and vice-versa.
    pub fn opposite(self) -> Self {
        match self {
            Lit::Pos(v) => Lit::Neg(v),
            Lit::Neg(v) => Lit::Pos(v),
        }
    }
}

/// A `Prop` represents a variable that can be assigned
/// a value in a SAT constraint.
pub trait InternalProp: Ord + Eq + Clone + Any {
    /// Add yourself to the given solver.
    fn add_to_prop_map(self, solver: &mut Solver) -> Var;
}

impl InternalProp for Var {
    fn add_to_prop_map(self, _solver: &mut Solver) -> Var {
        // Leave the value unchanged.
        self
    }
}

/// A `DefinedProp` is a prop that comes along with a definition,
/// which is just a set of clauses that are added as soon as it's mentioned.
///
/// To use them, add them as `Defined(my_prop)` instead of plain `my_prop`.
pub trait DefinedProp: Ord + Eq + Clone + Any {
    /// Adds constraints (in a "blank" condition context) to the given prop;
    /// this will be called as soon as the prop is "mentioned" in any clause.
    fn define_prop(self, solver: &mut Solver);
}

#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd, Hash, Debug)]
pub struct Defined<P: DefinedProp>(pub P);

impl<P: DefinedProp> InternalProp for Defined<P> {
    fn add_to_prop_map(self, solver: &mut Solver) -> Var {
        let def = self.0.clone();
        // Look up this value in the solver's map.
        // If not present, insert it with a new `Var` index.
        // Otherwise, return the existing value.
        let type_id: TypeId = TypeId::of::<P>();

        let mut inserted = false;
        let created_var = *solver
            .prop_map
            .prop_indexes
            .entry(type_id)
            .or_insert_with(|| {
                let new_map: BTreeMap<P, Var> = BTreeMap::new();
                Arc::new(Mutex::new(new_map))
            })
            .lock()
            .expect("lock is not poisoned")
            .downcast_mut::<BTreeMap<P, Var>>()
            .unwrap()
            .entry(self.0)
            .or_insert_with(|| {
                inserted = true;
                solver.prop_map.fresh_index += 1;
                Var(solver.prop_map.fresh_index)
            });

        if inserted {
            def.define_prop(solver);
        }

        created_var
    }
}

/// `VarOrProp` is just a convenient type to mix your `Prop`
/// types with `Var`s that you've already converted.
#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum VarOrProp<P: InternalProp> {
    Prop(P),
    Var(Var),
}

impl<P: InternalProp> From<P> for VarOrProp<P> {
    fn from(prop: P) -> Self {
        Self::Prop(prop)
    }
}

impl Var {
    /// This is a convenient function for converting a `Var` into a `VarOrProp`.
    pub fn just_var<P: InternalProp>(self) -> VarOrProp<P> {
        VarOrProp::Var(self)
    }
}

impl<P: InternalProp> InternalProp for VarOrProp<P> {
    fn add_to_prop_map(self, solver: &mut Solver) -> Var {
        match self {
            Self::Prop(prop) => prop.add_to_prop_map(solver),
            Self::Var(v) => v.add_to_prop_map(solver),
        }
    }
}

/// Implement this trait for your types to allow them as propositions
/// in your SAT constraints.
pub trait Prop: Clone + Eq + Ord + Any {
    fn validate(&self) {}
}

impl<P: Prop> InternalProp for P {
    fn add_to_prop_map(self, solver: &mut Solver) -> Var {
        self.validate();
        // Look up this value in the solver's map.
        // If not present, insert it with a new `Var` index.
        // Otherwise, return the existing value.
        let type_id: TypeId = TypeId::of::<P>();

        *solver
            .prop_map
            .prop_indexes
            .entry(type_id)
            .or_insert_with(|| {
                let new_map: BTreeMap<P, Var> = BTreeMap::new();
                Arc::new(Mutex::new(new_map))
            })
            .lock()
            .expect("lock is not poisoned")
            .downcast_mut::<BTreeMap<P, Var>>()
            .unwrap()
            .entry(self)
            .or_insert_with(|| {
                solver.prop_map.fresh_index += 1;
                Var(solver.prop_map.fresh_index)
            })
    }
}

/// A `Solver` is used to build and (and later solve) SAT constraints.
#[derive(Default, Debug, Clone)]
pub struct Solver {
    /// A clause is a set of literals; each literal is a positive or negative integer (e.g. 5 or -5).
    /// The number 0 should not appear anywhere in any clause.
    ///
    /// In each clause, at least one literal must hold in a satisfying assignment.
    clauses: BTreeSet<BTreeSet<i32>>,

    /// This map "remembers" all of the `Prop`s used in building this constraint problem.
    /// It acts as a (dynamic) map from any prop type to `Var`.
    prop_map: PropMap<Var>,
}

impl Solver {
    /// Creates a new empty `Solver`.
    pub fn new() -> Solver {
        Self::default()
    }
}

#[derive(Clone, Debug)]
pub struct PropMap<T> {
    /// This index is used to assign props to numeric entries.
    fresh_index: i32,
    prop_indexes: BTreeMap<TypeId, Arc<Mutex<dyn Any>>>,
    item_type: std::marker::PhantomData<T>,
}
impl<T> Default for PropMap<T> {
    fn default() -> Self {
        PropMap {
            fresh_index: Default::default(),
            prop_indexes: Default::default(),
            item_type: std::marker::PhantomData,
        }
    }
}

/// a `ConditionalClauseBuilder` struct has a reference to another `ClauseBuilder`;
/// it will implicitly add the given constraint as a hypothesis to any clauses added.
///
/// Create it by calling `.when` or `.when_all` on a `&mut dyn ClauseBuilder`.
pub struct ConditionalClauseBuilder<'a> {
    pub negative_condition: Vec<Lit<Var>>,
    pub parent: &'a mut dyn ClauseBuilder,
}

impl<'a> ClauseBuilder for ConditionalClauseBuilder<'a> {
    fn add_lits_dimacs_clause(&mut self, lits: &[Lit<Var>]) {
        // Adds all of the conditioned values.
        let mut lits = lits.to_vec();
        lits.extend_from_slice(&self.negative_condition);
        self.parent.add_lits_dimacs_clause(&lits);
    }
    fn original_solver(&mut self) -> &mut Solver {
        self.parent.original_solver()
    }
}

/// A `ClauseBuilder` allows clauses to be added.
///
/// This trait is object-safe! Ask for a `&mut dyn ClauseBuilder`.
///
/// All of the helper functions that you should actually call
/// are on `ClauseBuilderHelper`.
pub trait ClauseBuilder {
    fn add_lits_dimacs_clause(&mut self, lits: &[Lit<Var>]);
    fn original_solver(&mut self) -> &mut Solver;
}

impl ClauseBuilder for Solver {
    fn add_lits_dimacs_clause(&mut self, lits: &[Lit<Var>]) {
        let lits: BTreeSet<i32> = lits.iter().copied().map(|lit| lit.dimacs_int()).collect();
        self.clauses.insert(lits);
    }
    fn original_solver(&mut self) -> &mut Solver {
        self
    }
}

fn var_lit<P>(solver: &mut Solver, lit: Lit<P>) -> Lit<Var>
where
    P: InternalProp,
{
    lit.map(|item| item.add_to_prop_map(solver.original_solver()))
}

fn var_lits<P>(solver: &mut Solver, lits: impl IntoIterator<Item = Lit<P>>) -> Vec<Lit<Var>>
where
    P: InternalProp,
{
    lits.into_iter()
        .map(|lit| lit.map(|item| item.add_to_prop_map(solver.original_solver())))
        .collect()
}

/// This trait defines all of the helper functions used to build complex clauses.
/// This methods are defined here instead of on `ClauseBuilder` directly so that `ClauseBuilder` remains object-safe.
pub trait ClauseBuilderHelper: ClauseBuilder {
    /// Resolves the given prop into a `Var`.
    fn resolve_prop(&mut self, prop: impl InternalProp) -> Var {
        prop.add_to_prop_map(self.original_solver())
    }

    /// Resolves the given literal into a `Lit<Var>`.
    fn resolve_lit(&mut self, lit: Lit<impl InternalProp>) -> Lit<Var> {
        lit.map(|prop| self.resolve_prop(prop))
    }

    /// Adds the given clause to the solver.
    /// All items in the clause are converted from any `InternalProp` to the concrete `Var`.
    fn add_clause<Prop>(&mut self, lits: impl IntoIterator<Item = Lit<Prop>>)
    where
        Prop: InternalProp,
    {
        let lits: Vec<Lit<Var>> = var_lits(self.original_solver(), lits);
        self.add_lits_dimacs_clause(&lits);
    }

    /// Returns a `ConditionClauseBuilder` whose clauses are only enforced when the given condition holds.
    fn when(&mut self, condition: Lit<impl InternalProp>) -> ConditionalClauseBuilder;

    /// Returns a `ConditionClauseBuilder` whose clauses are only enforced when all of the given conditions hold.
    fn when_all(
        &mut self,
        condition: impl IntoIterator<Item = Lit<impl InternalProp>>,
    ) -> ConditionalClauseBuilder;

    /// Asserts that the single literal holds.
    fn then(&mut self, lit: Lit<impl InternalProp>) {
        self.add_clause([lit]);
    }

    /// Asserts that each of the literals hold.
    fn then_all(&mut self, lits: impl IntoIterator<Item = Lit<impl InternalProp>>) {
        for lit in lits.into_iter() {
            self.then(lit);
        }
    }

    /// Asserts that at least one of the literals is true.
    /// (this function is identical to `add_clause`)
    fn at_least_one(&mut self, lits: impl IntoIterator<Item = Lit<impl InternalProp>>) {
        self.add_clause(lits);
    }

    /// Asserts that if `a` holds, then `b` does.
    /// You can also write this as `self.when(a).then(b)`.
    fn implies(&mut self, a: Lit<impl InternalProp>, b: Lit<impl InternalProp>) {
        self.when(a).then(b);
    }

    /// Asserts that the two literals are equivalent (both hold or neither do).
    fn equiv(&mut self, a: Lit<impl InternalProp>, b: Lit<impl InternalProp>) {
        let a = var_lit(self.original_solver(), a);
        let b = var_lit(self.original_solver(), b);
        self.implies(a, b);
        self.implies(b, a);
    }

    /// Asserts that the first literal is equivalent to all of the second literals holding.
    fn equiv_and(
        &mut self,
        a: Lit<impl InternalProp>,
        bs: impl IntoIterator<Item = Lit<impl InternalProp>>,
    ) {
        let a = var_lit(self.original_solver(), a);
        let bs = var_lits(self.original_solver(), bs);

        // a => (b1 & ... & bn)
        self.when(a).then_all(bs.iter().copied());

        // (b1 & ... & bn) => a
        self.when_all(bs).then(a);
    }

    /// Asserts that the first literal is equivalent to at least one of the second literals holding.
    fn equiv_or(
        &mut self,
        a: Lit<impl InternalProp>,
        bs: impl IntoIterator<Item = Lit<impl InternalProp>>,
    ) {
        let a = var_lit(self.original_solver(), a);
        let bs = var_lits(self.original_solver(), bs);

        // a => (b1 | ... | bn)
        self.when(a).at_least_one(bs.iter().copied());

        // (b1 | ... | bn) => a
        // (b1 => a) & ... & (bn => a)
        for &b in bs.iter() {
            self.when(b).then(a);
        }
    }

    /// Asserts that at most one of the given lits holds.
    /// This function uses a worst-case linear encoding.
    fn at_most_one(&mut self, lits: impl IntoIterator<Item = Lit<impl InternalProp>>) {
        let lits = var_lits(self.original_solver(), lits);
        if lits.len() <= 1 {
            // No constraints are needed.
            return;
        }
        if lits.len() == 2 {
            self.at_least_one([lits[0].opposite(), lits[1].opposite()]);
            return;
        }
        // Otherwise, fall back to the defined 'AtMostOne' prop.
        self.then(Lit::Pos(Defined(AtMostOne(lits))));
    }

    /// Asserts that exactly one of the given lits holds.
    /// This function uses a worst-case linear encoding.
    fn exactly_one(&mut self, lits: impl IntoIterator<Item = Lit<impl InternalProp>>) {
        let lits = var_lits(self.original_solver(), lits);
        self.at_least_one(lits.iter().copied());
        self.at_most_one(lits);
    }
}

impl ClauseBuilder for &mut dyn ClauseBuilder {
    fn add_lits_dimacs_clause(&mut self, lits: &[Lit<Var>]) {
        (*self).add_lits_dimacs_clause(lits);
    }
    fn original_solver(&mut self) -> &mut Solver {
        (*self).original_solver()
    }
}
impl<T: ClauseBuilder> ClauseBuilderHelper for T {
    fn when(&mut self, condition: Lit<impl InternalProp>) -> ConditionalClauseBuilder {
        let lit: Lit<Var> = condition.map(|prop| prop.add_to_prop_map(self.original_solver()));

        ConditionalClauseBuilder {
            negative_condition: vec![lit.opposite()],
            parent: self,
        }
    }
    fn when_all(
        &mut self,
        conditions: impl IntoIterator<Item = Lit<impl InternalProp>>,
    ) -> ConditionalClauseBuilder {
        let lits: Vec<Lit<Var>> = var_lits(
            self.original_solver(),
            conditions.into_iter().map(|lit| lit.opposite()),
        );

        ConditionalClauseBuilder {
            negative_condition: lits,
            parent: self,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct AtMostOne(pub Vec<Lit<Var>>);

impl DefinedProp for AtMostOne {
    fn define_prop(self, solver: &mut Solver) {
        let v = solver.resolve_prop(Defined(self.clone()));
        if self.0.len() <= 1 {
            // It is always true:
            solver.then(Lit::Pos(v));
            return;
        }

        // at_least_one_left[i] <==> (prop[0] | prop[1] | ... | prop[i])
        let at_least_one_left: Vec<Lit<Helper>> = (0..self.0.len())
            .map(|i| Lit::Pos(Helper(v, "left", i)))
            .collect::<Vec<_>>();

        for i in 0..at_least_one_left.len() {
            let item: Lit<Var> = self.0[i];
            if i == 0 {
                solver.equiv(at_least_one_left[i], item);
            } else {
                let prev = solver.resolve_lit(at_least_one_left[i - 1]);
                solver.equiv_or(at_least_one_left[i], [prev, item]);
            }
        }

        // conflict[i] <==> (prop[i] & at_least_one_left[i-1])
        let conflict: Vec<Lit<Helper>> = (0..self.0.len())
            .map(|i| Lit::Pos(Helper(v, "conflict", i)))
            .collect::<Vec<_>>();

        for i in 0..conflict.len() {
            if i > 0 {
                let item: Lit<Var> = self.0[i];
                let prev = solver.resolve_lit(at_least_one_left[i - 1]);
                solver.equiv_and(conflict[i], [item, prev]);
            }
        }

        solver.equiv_or(Lit::Neg(v), conflict[1..].iter().copied());
    }
}

// This type is used for generic auxiliary variables.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
struct Helper(Var, &'static str, usize);
impl Prop for Helper {}

impl Solver {
    /// Uses the `splr` crate to solve the given constraints.
    pub fn solve_splr(
        &self,
    ) -> Result<Option<std::collections::HashMap<Var, bool>>, splr::SolverError> {
        let clauses: Vec<Vec<i32>> = self
            .clauses
            .iter()
            .map(|clause| clause.iter().copied().collect())
            .collect();
        match splr::Certificate::try_from(clauses) {
            Ok(splr::Certificate::SAT(answer)) => {
                let mut result: std::collections::HashMap<Var, bool> =
                    std::collections::HashMap::new();
                for v in answer {
                    assert!(v != 0);
                    result.insert(Var(v.abs()), v > 0);
                }
                Ok(Some(result))
            }
            Ok(splr::Certificate::UNSAT) => Ok(None),
            Err(err) => Err(err),
        }
    }
}
