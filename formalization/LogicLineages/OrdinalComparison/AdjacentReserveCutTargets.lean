module
public import LogicLineages.OrdinalComparison.AdjacentPackedTargets
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Literal reserve cut in paper07 adjacent proof 556–580. The full prefix
trace, actual counts and strict tail inequality are conclusions, not oracles. -/
def ActualAdjacentReserveCut : Prop :=
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
      let remainder := b+(k : Ordinal)
      let A := pi*(R : Ordinal)+remainder
      let D := actualSuffixKernelCount L.1.repr e t
      let Z := actualSuffixKernel L.1.repr e t
      let q := actualControlledCount (compensatedPrefixControl p) remainder
      let V := (Phi^[q]) B'
      let n := V-p
      0 < D ∧ D ≤ q+1 ∧
      q ≤ actualControlledCount (compensatedPrefixControl c) A ∧
      (∀ i : Nat, i ≤ q → actualControlledStateAfter (compensatedPrefixControl c) A i =
        pi*(R : Ordinal)+actualControlledStateAfter (compensatedPrefixControl p) remainder i) ∧
      p ≤ V ∧ n+p=V ∧
      actualControlledStateAfter (compensatedPrefixControl c) A q = pi*(R : Ordinal)+(n : Ordinal) ∧
      Z+D < n

end LogicLineages.OrdinalComparison.Targets
