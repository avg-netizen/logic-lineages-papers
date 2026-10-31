module
public import LogicLineages.OrdinalComparison.WWEncodedCounterBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation
/-- A bound indexed by original frontend inputs, not by compiled-query image
representatives. This distinction matters when a compiler has repeated outputs. -/
def FrontendCoordinateBound (frontend : Nat → Nat) : Prop :=
  ∃ b : Nat → Nat, Computable b ∧ ∀ q, ¬ CodedQueryGood (frontend q) →
    ∃ xs : List Nat, xs.length = queryArity (frontend q) ∧
      (∀ x ∈ xs, x + 1 ≤ b q) ∧ codedQueryAt (frontend q) xs = false

def EffectiveFrontendCounterEnumerable : Prop :=
  ∀ frontend : Nat → Nat, Computable frontend →
    REPred (fun q => ¬ CodedQueryGood (frontend q))

def EffectiveFrontendDecisionIffCoordinateBound : Prop :=
  ∀ frontend : Nat → Nat, Computable frontend →
    (ComputablePred (fun q => CodedQueryGood (frontend q)) ↔ FrontendCoordinateBound frontend)
end LogicLineages.OrdinalComparison.Source.Targets
