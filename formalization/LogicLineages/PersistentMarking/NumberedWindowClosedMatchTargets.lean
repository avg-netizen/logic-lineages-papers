module
public import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowNumericalMatching
public import LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClosedMatchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowNumericalMatching
open NumberedWindowInternalMatchReductionTargets (suppliedMatch)
def ClosedMatch (r p : Program 3) (body : Positive (Fin 1)) : Prop :=
  ∀ (α : Type) (f g u v w : Nat), Nonempty (Derivation body ([] : List (Formula α))
    ((accepts r (numeral f) (numeral w) (numeral g) ⊓ accepts p (numeral g) (numeral u) (numeral v)).imp
      (suppliedMatch p r (numeral f) (numeral u) (numeral v))))
def ClosedDerivations : Prop :=
  ∀ (edge app : Nat → Nat → Nat → Bool) (r p : Program 3),
    (∀ x y z, evaluate r (x ::ᵥ y ::ᵥ z ::ᵥ nil) = (edge x y z).toNat) →
    (∀ x y z, evaluate p (x ::ᵥ y ::ᵥ z ::ᵥ nil) = (app x y z).toNat) →
    Matching edge app → ∀ body, ClosedMatch r p body
end LogicLineages.PersistentMarking.NumberedWindowClosedMatchTargets
