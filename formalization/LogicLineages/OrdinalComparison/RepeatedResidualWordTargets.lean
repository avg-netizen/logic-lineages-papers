module
public import LogicLineages.OrdinalComparison.RepeatedPrincipalWordTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Genuine retained-cut to repeated-word/full-terminal calibration used by
paper07 strict mass. Structural compatibility is paid in the proof; no count,
endpoint or word correctness hypothesis is part of this target. -/
def ActualRepeatedResidualWordCalibration : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → Ordinal.omega0^eta.1.repr*Ordinal.omega0 < epsilonZero →
    ∀ q c : Nat, ∀ r : Ordinal.{0}, r < Ordinal.omega0^eta.1.repr*Ordinal.omega0 →
      let theta := Ordinal.omega0^eta.1.repr
      let w := actualOrdinalNorm theta
      let p := c+q*w
      let B := p+actualOrdinalNorm r
      let C := actualControlledCount (compensatedPrefixControl p) r
      let U := (Phi^[C]) B
      let A := theta*(q : Ordinal)+r
      let g := compensatedPrefixControl c
      let word := principalKernelWord (List.replicate q eta.1) c
      C ≤ actualControlledCount g A ∧ actualPrincipalWordGenuine word U ∧
      (actualPrincipalWordRun word U).1 = c+actualOrdinalNorm
        (actualControlledStateAfter g A (actualControlledCount g A)) ∧
      (actualPrincipalWordRun word U).2+C=actualControlledCount g A

end LogicLineages.OrdinalComparison.Targets
