module
public import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets

/-- The existential binds the earlier application result. The free result v belongs
to the later function g; the scalar edge goes from the earlier result to v. -/
def matched (d : Data) (p : Program 3) (c : Nat) {α : Type}
    (f u v : OrdinaryArithmetic.Term α) : Formula α :=
  existsOne (accepts p (f.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0)) ⊓
    edge d false c (.var (.inr 0)) (v.relabel Sum.inl))

/-- A purely arithmetic open-term rule required by the arrow step.
It contains no computability formula or free inductive predicate. -/
def ApplicationEdgeMatching (d : Data) (p : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (f g u v : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody d c) Γ (edge d false c f g)) →
    Nonempty (Derivation (sourceBody d c) Γ (accepts p g u v)) →
    Nonempty (Derivation (sourceBody d c) Γ (matched d p c f u v))

def ComputabilityDownward : Prop :=
  ∀ (d : Data) (p : Program 3) (c : Nat), ApplicationEdgeMatching d p c →
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (f g : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody d c) Γ (formula p τ f)) →
    Nonempty (Derivation (sourceBody d c) Γ (edge d false c f g)) →
    Nonempty (Derivation (sourceBody d c) Γ (formula p τ g))

end LogicLineages.PersistentMarking.NumberedWindowInternalDownwardTargets
