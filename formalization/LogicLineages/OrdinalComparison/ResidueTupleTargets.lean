module
public import LogicLineages.OrdinalComparison.ResidueTupleDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! First sentence of source thm:actual-period: exact genuine residue-tuple
Frobenius period. The second sentence, concerning complete rational Cartier
states, is not a consequence of these targets alone and remains separate. -/
def ActualLinkedPrimitiveRootExists : Prop :=
  ∀ u : Nat, 5 ≤ u → Nonempty (ActualPrimitiveRootIndex u)

def ActualResidueTupleIterate : Prop :=
  ∀ u : Nat, ∀ v : ActualPrimitiveRootIndex u → ActualResidueField,
    ∀ s : Nat, ∀ z : ActualPrimitiveRootIndex u,
      ((actualResidueTupleFrobenius u)^[s] v) z = v z ^ (2 ^ s)

def ActualResidueTupleExactPeriod : Prop :=
  ∀ u : Nat, 5 ≤ u →
    Function.minimalPeriod (actualResidueTupleFrobenius u) (actualResidueTuple u) =
      2 * actualLinkedHalfExponent u

def FullActualSourceResidueTuplePeriod : Prop :=
  ∀ v : Nat, 4 ≤ v →
    Function.minimalPeriod (actualResidueTupleFrobenius (Phi v)) (actualResidueTuple (Phi v)) =
      2 * actualLinkedHalfExponent (Phi v)

end LogicLineages.OrdinalComparison.Targets
