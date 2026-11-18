module
public import LogicLineages.OrdinalComparison.ResidueTupleTargets

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts.Targets
open LogicLineages.OrdinalComparison

def RootExists : Prop := ∀ u : Nat, 5 ≤ u → Nonempty (ActualPrimitiveRootIndex u)

def ActualIterate : Prop := ∀ u : Nat,
  ∀ b : ActualPrimitiveRootIndex u → ActualResidueField, ∀ s : Nat,
    ∀ z : ActualPrimitiveRootIndex u,
      ((actualResidueTupleFrobenius u)^[s] b) z = b z ^ (2 ^ s)

def ActualUpper : Prop := ∀ u : Nat, 5 ≤ u →
  (actualResidueTupleFrobenius u)^[2 * actualLinkedHalfExponent u] (actualResidueTuple u) =
    actualResidueTuple u

def ActualMidpoint : Prop := ∀ u : Nat, 5 ≤ u →
  (actualResidueTupleFrobenius u)^[actualLinkedHalfExponent u] (actualResidueTuple u) ≠
    actualResidueTuple u

def ActualSmall : Prop := ∀ u : Nat, 5 ≤ u → ∀ s : Nat,
  0 < s → 3 * s ≤ 2 * actualLinkedHalfExponent u →
    (actualResidueTupleFrobenius u)^[s] (actualResidueTuple u) ≠ actualResidueTuple u

def ActualExact : Prop := ∀ u : Nat, 5 ≤ u →
  Function.minimalPeriod (actualResidueTupleFrobenius u) (actualResidueTuple u) =
    2 * actualLinkedHalfExponent u
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts.Targets
