module
public import LogicLineages.OrdinalComparison.AdjacentPackedDefinitions
public import LogicLineages.OrdinalComparison.AffordableLeadingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 adjacent proof 538–555: exact affordable leading and packed first
suffix, with actual lower suffix norm B−e/global B. Integer source subtraction
is represented by (B′+e)−(B+p), with nontruncation proved below. -/
def ActualAdjacentLeadingCoverage : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t e : Nat, profileAdjacentThreshold L E ≤ t → e + actualOrdinalNorm L.1.repr ≤ t →
      let pi := (profileLeadingNote (maximumPredecessor L (Phi t-e))).1.repr
      2 ≤ Phi t-e ∧ Ordinal.omega0 ≤ pi ∧ pi < L.1.repr ∧
      actualOrdinalNorm pi ≤ Phi t ∧
      (∃ beta : Ordinal.{0}, 0 < beta ∧ pi = Ordinal.omega0 ^ beta) ∧
      ∀ rho ∈ profileBoundWord E, actualProfileLeadingMonomial rho ≤ pi

def ActualAdjacentPackedState : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t c e : Nat, profileAdjacentThreshold L E ≤ t →
      c + actualOrdinalNorm L.1.repr ≤ t+1 → e + actualOrdinalNorm L.1.repr ≤ t →
      let B := Phi t
      let B' := Phi (t+1)
      let b := actualMaximumPredecessor L.1.repr (B-e)
      let pi := (profileLeadingNote (maximumPredecessor L (B-e))).1.repr
      let R := profileReserveBlocks (profileBoundWord E)
      let p := c + R * actualOrdinalNorm pi
      let k := (B'+e)-(B+p)
      let A := pi * (R : Ordinal) + (b + (k : Ordinal))
      let Q := actualMaximumPredecessor L.1.repr (B'-c)
      B+p ≤ B'+e ∧ k+(B+p) = B'+e ∧ p ≤ (R+1)*B ∧
      b < pi * Ordinal.omega0 ∧ A < L.1.repr ∧
      actualOrdinalNorm b = B-e ∧ e + actualOrdinalNorm b = B ∧
      p + actualOrdinalNorm (b + (k : Ordinal)) = B' ∧
      actualOrdinalNorm A = B'-c ∧ A ≤ Q ∧ actualOrdinalNorm Q = B'-c

end LogicLineages.OrdinalComparison.Targets
