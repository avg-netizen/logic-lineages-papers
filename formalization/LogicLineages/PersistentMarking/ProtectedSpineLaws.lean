import LogicLineages.PersistentMarking.ProtectedSpineInterpreter
import LogicLineages.PersistentMarking.ProtectedSpineEnvironmentTargets
import LogicLineages.PersistentMarking.HereditaryOrderTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineLaws
open Spine DecisionInventory DecisionPorts FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics ProtectedSpineEnvironment ProtectedSpineInterpreterCore
open ProtectedSpineEnvironmentTargets

structure Assignments where
  free : FreeValues
  bound : BoundValues

def Assignments.restrict (E : Environment) (Γ Δ : Context) (a : Assignments) : Assignments :=
  ⟨weakenFree E Γ Δ a.free,weakenBound E Γ Δ a.bound⟩

def Assignments.push (a : Assignments) (σ : Ty) (c : Code) : Assignments :=
  ⟨a.free,(σ,c)::a.bound⟩

def InputValid (E : Environment) (Γ : Context) (a : Assignments) : Prop :=
  WellFormed E.types E.ports Γ ∧ FreeValid E Γ a.free ∧ BoundValid E Γ a.bound

def InputLE (E : Environment) (Γ : Context) (a b : Assignments) : Prop :=
  (∀ σ x, (descriptor E σ).le Γ (freeCode E Γ a.free σ x) (freeCode E Γ b.free σ x) = true) ∧
  (∀ σ i, (descriptor E σ).le Γ (boundCode E Γ a.bound σ i) (boundCode E Γ b.bound σ i) = true)

def valueAt (ev : Evaluation) (Γ : Context) (a : Assignments) : Value :=
  ev.value Γ a.free a.bound

def codeAt (E : Environment) (σ : Ty) (ev : Evaluation) (Γ : Context) (a : Assignments) : Code :=
  code E σ Γ (valueAt ev Γ a)

def nonemptyAt (E : Environment) (ev : Evaluation) (Γ : Context) (a : Assignments) (consumed : Nat)
    (ds : List Ty) (τ : Ty) (xs : List Code) : Code :=
  match ds,xs with
  | d::ds,x::xs => ev.nonempty Γ a.free a.bound consumed d x ds xs τ
  | _,_ => StructuralActions.bottom E τ Γ

structure EvaluationLaws (E : Environment) (σ : Ty) (ev : Evaluation) : Prop where
  valid : ∀ Γ a, InputValid E Γ a → Valid E σ Γ (valueAt ev Γ a)
  natural : ∀ Γ Δ a, InputValid E Γ a → WellFormed E.types E.ports Δ → Extends Γ Δ →
    ValueEq E σ Δ (valueAt ev Γ a) (valueAt ev Δ (a.restrict E Γ Δ))
  monotone : ∀ Γ a b, InputValid E Γ a → InputValid E Γ b → InputLE E Γ a b →
    HereditaryOrderTargets.SemanticLE E σ Γ (valueAt ev Γ a) (valueAt ev Γ b)
  callValid : ∀ Γ a k ds τ xs, InputValid E Γ a → (ds,τ) ∈ fullPrefixes σ → TupleValues E Γ ds xs →
    nonemptyAt E ev Γ a k ds τ xs ∈ (descriptor E τ).carriers Γ
  callNatural : ∀ Γ Δ a k ds τ xs, InputValid E Γ a → WellFormed E.types E.ports Δ → Extends Γ Δ →
    (ds,τ) ∈ fullPrefixes σ → TupleValues E Γ ds xs →
    (descriptor E τ).restrict Γ Δ (nonemptyAt E ev Γ a k ds τ xs) =
      nonemptyAt E ev Δ (a.restrict E Γ Δ) k ds τ (restrictValues E Γ Δ ds xs)
  callMonotone : ∀ Γ a b k ds τ xs ys, InputValid E Γ a → InputValid E Γ b → InputLE E Γ a b →
    (ds,τ) ∈ fullPrefixes σ → TupleValues E Γ ds xs → TupleValues E Γ ds ys → ValuesLE E Γ ds xs ys →
    (descriptor E τ).le Γ (nonemptyAt E ev Γ a k ds τ xs) (nonemptyAt E ev Γ b k ds τ ys) = true

def Covered (E : Environment) (sourceHeads : List Head) (q : Expr) : Prop :=
  (∀ τ, τ ∈ auxiliarySupport q → τ ∈ E.types) ∧
  (∀ f, f ∈ heads q → f ∈ sourceHeads)

def ArgsCovered (E : Environment) (sourceHeads : List Head) (qs : Args) : Prop :=
  (∀ τ, τ ∈ auxiliaryArgs qs → τ ∈ E.types) ∧
  (∀ f, f ∈ headsArgs qs → f ∈ sourceHeads)

abbrev Arguments := Context → FreeValues → BoundValues → BoundValues

def argumentValues (args : Arguments) (Γ : Context) (a : Assignments) : BoundValues :=
  args Γ a.free a.bound

structure ArgumentLaws (E : Environment) (args : Arguments) (types : List Ty) : Prop where
  types_eq : ∀ Γ a, (argumentValues args Γ a).map Prod.fst = types
  valid : ∀ Γ a, InputValid E Γ a → TupleValues E Γ types ((argumentValues args Γ a).map Prod.snd)
  natural : ∀ Γ Δ a, InputValid E Γ a → WellFormed E.types E.ports Δ → Extends Γ Δ →
    weakenBound E Γ Δ (argumentValues args Γ a) = argumentValues args Δ (a.restrict E Γ Δ)
  monotone : ∀ Γ a b, InputValid E Γ a → InputValid E Γ b → InputLE E Γ a b →
    ValuesLE E Γ types ((argumentValues args Γ a).map Prod.snd) ((argumentValues args Γ b).map Prod.snd)

def InterpretationLaws : Prop :=
  ∀ S E heads M C q σ, MarkedConstructorTargets.PrefixClosed E →
    M ∈ MarkedFamilyCoherence.retained E heads →
    Typed C q σ → Covered E heads q →
    EvaluationLaws E σ (ProtectedSpineInterpreter.evaluate S E heads M q)

end LogicLineages.PersistentMarking.ProtectedSpineLaws
