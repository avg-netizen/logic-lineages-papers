module
public import LogicLineages.OrdinalComparison.LimitMassFirstTargets
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 limitmass623–649: literal second-step packing and actual second
maximum calibration. Nontruncation and all count/exit laws are conclusions. -/
def ActualLimitMassPackedState : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0^beta → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L.1.repr E → ∀ t c e : Nat,
    profileLimitMassThreshold L E ≤ t → c < e → e+actualOrdinalNorm L.1.repr ≤ t →
      let B := Phi t
      let C := Phi B
      let pi_e := actualMaximumPredecessor L.1.repr (B-e)
      let pi_c := actualMaximumPredecessor L.1.repr (B-c)
      let w := actualOrdinalNorm pi_e
      let R := profileReserveBlocks (profileBoundWord E)
      let p := c+R*w
      let k := C-(c+(R+1)*w)
      let r := pi_e+(k : Ordinal)
      let A := pi_e*(R : Ordinal)+r
      let Q := actualMaximumPredecessor pi_c (C-c)
      c+(R+1)*w ≤ C ∧ k+(c+(R+1)*w)=C ∧
      A = pi_e*((R+1 : Nat) : Ordinal)+(k : Ordinal) ∧ A < pi_c ∧
      actualOrdinalNorm A=C-c ∧ actualOrdinalNorm Q=C-c ∧ A ≤ Q ∧
      p+actualOrdinalNorm r=C ∧ p ≤ (R+1)*B

def ActualLimitMassSecondMaximum : Prop :=
  ∀ L : NONote, ∀ beta : Ordinal.{0}, Order.IsSuccLimit beta →
    L.1.repr = Ordinal.omega0^beta → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L.1.repr E → ∀ t c e : Nat,
    profileLimitMassThreshold L E ≤ t → c < e → e+actualOrdinalNorm L.1.repr ≤ t →
      let B := Phi t
      let C := Phi B
      let pi_c := actualMaximumPredecessor L.1.repr (B-c)
      let Q := actualMaximumPredecessor pi_c (C-c)
      let g := compensatedPrefixControl c
      actualControlledStateAfter g (actualSuffixKernelInitial L.1.repr c t) 2=Q ∧
      actualSuffixKernelCount L.1.repr c t=actualControlledCount g Q+2 ∧
      actualSuffixKernel L.1.repr c t=c+actualOrdinalNorm
        (actualControlledStateAfter g Q (actualControlledCount g Q))

end LogicLineages.OrdinalComparison.Targets
