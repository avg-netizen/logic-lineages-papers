module
public import LogicLineages.OrdinalComparison.LimitMassPackedTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Actual reserve cut in the limitmass proof632–649, with literal global C
and actual lower first monomial. No cut/count/endpoint or growth oracle. -/
def ActualLimitMassReserveCut : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0^beta → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L.1.repr E → ∀ t c e : Nat,
    profileLimitMassThreshold L E ≤ t → c < e → e+actualOrdinalNorm L.1.repr ≤ t →
      let B := Phi t
      let C := Phi B
      let pi_e := actualMaximumPredecessor L.1.repr (B-e)
      let w := actualOrdinalNorm pi_e
      let R := profileReserveBlocks (profileBoundWord E)
      let p := c+R*w
      let k := C-(c+(R+1)*w)
      let r := pi_e+(k : Ordinal)
      let A := pi_e*(R : Ordinal)+r
      let D := actualSuffixKernelCount L.1.repr e t
      let Z := actualSuffixKernel L.1.repr e t
      let q := actualControlledCount (compensatedPrefixControl p) r
      let V := (Phi^[q]) C
      let n := V-p
      0 < D ∧ D ≤ q+1 ∧ q ≤ actualControlledCount (compensatedPrefixControl c) A ∧
      (∀ i : Nat, i ≤ q → actualControlledStateAfter (compensatedPrefixControl c) A i =
        pi_e*(R : Ordinal)+actualControlledStateAfter (compensatedPrefixControl p) r i) ∧
      p ≤ V ∧ n+p=V ∧
      actualControlledStateAfter (compensatedPrefixControl c) A q=pi_e*(R : Ordinal)+(n : Ordinal) ∧
      Z+D < n

end LogicLineages.OrdinalComparison.Targets
