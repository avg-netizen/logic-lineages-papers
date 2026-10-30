module
public import LogicLineages.OrdinalComparison.LimitMassFirstDefinitions
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 limitmass, literal first suffixes and effective threshold (6.5).
All masses range over the genuine domain; saturation, strictness and coverage
are proved conclusions, not added implementation fields. -/
def ActualLimitMassFirstSuffixes : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0 ^ beta →
    ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t c e : Nat, profileLimitMassThreshold L E ≤ t → c < e →
      e + actualOrdinalNorm L.1.repr ≤ t →
      let B := Phi t
      let pi_e := actualMaximumPredecessor L.1.repr (B-e)
      let pi_c := actualMaximumPredecessor L.1.repr (B-c)
      Ordinal.omega0 ≤ pi_e ∧ pi_e < pi_c ∧ pi_c < L.1.repr ∧
      actualOrdinalNorm pi_e = B-e ∧ actualOrdinalNorm pi_c = B-c ∧
      e+actualOrdinalNorm pi_e=B ∧ c+actualOrdinalNorm pi_c=B ∧
      (∃ delta : Ordinal.{0}, 0 < delta ∧ pi_e=Ordinal.omega0^delta) ∧
      (∃ delta : Ordinal.{0}, 0 < delta ∧ pi_c=Ordinal.omega0^delta) ∧
      ∀ rho ∈ profileBoundWord E, actualProfileLeadingMonomial rho ≤ pi_e

end LogicLineages.OrdinalComparison.Targets
