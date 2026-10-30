module
public import LogicLineages.OrdinalComparison.RepeatedResidualWordTargets
public import LogicLineages.OrdinalComparison.SuccessorMassCutProof
public import LogicLineages.OrdinalComparison.RepeatedPrincipalWordProof
public import LogicLineages.OrdinalComparison.AdjacentTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualRepeatedResidualWordCalibration : Targets.ActualRepeatedResidualWordCalibration := by
  intro eta he hL q c r hr
  dsimp only
  let theta := Ordinal.omega0^eta.1.repr
  let w := actualOrdinalNorm theta
  let p := c+q*w
  let B := p+actualOrdinalNorm r
  let C := actualControlledCount (compensatedPrefixControl p) r
  let U := (Phi^[C]) B
  let A := theta*(q : Ordinal)+r
  let g := compensatedPrefixControl c
  let word := principalKernelWord (List.replicate q eta.1) c
  have htheta : theta < epsilonZero := (Ordinal.le_mul_left theta Ordinal.omega0_pos).trans_lt hL
  have hrE := hr.trans hL
  have hrbound : r < Ordinal.omega0^(eta.1.repr+1) := by rw [Ordinal.opow_add_one]; exact hr
  have hc := actualCompensatedPrincipalRetainedCut eta.1.repr he htheta q c B r hrE hrbound rfl
  have hCU : p ≤ U := hc.2.2.1
  have hend : actualControlledStateAfter g A C=theta*(q : Ordinal)+((U-p : Nat) : Ordinal) := hc.2.2.2.2
  have hpm := reserveStagePrincipalMultipleFacts eta.1.repr htheta q
  have hmin : actualMinExponentAtLeast (theta*(q : Ordinal)) eta.1.repr := by
    apply (actualMinExponentDivisibility _ hpm.1 _).2
    exact dvd_mul_right _ _
  have hA := actualDivisiblePrefixNormAddition (theta*(q : Ordinal)) r hpm.1 hrE
    eta.1.repr (by exact dvd_mul_right _ _) hrbound
  have hrun := actualRepeatedPrincipalWordRun eta he q c (U-p)
  have hseed : c+q*w+(U-p)=U := by omega
  dsimp only at hrun
  change actualPrincipalWordRun word (c+q*w+(U-p)) =
    (c+actualOrdinalNorm (actualControlledStateAfter g (theta*(q : Ordinal)+((U-p : Nat) : Ordinal))
      (actualControlledCount g (theta*(q : Ordinal)+((U-p : Nat) : Ordinal)))),
      actualControlledCount g (theta*(q : Ordinal)+((U-p : Nat) : Ordinal))) ∧
    actualPrincipalWordGenuine word (c+q*w+(U-p)) at hrun
  rw [hseed, ← hend] at hrun
  have hept := actualControlledEndpointAlongTrace g A hA.1 C hc.1
  have hcount := actualControlledCountTraceDecomposition g A hA.1 C hc.1
  refine ⟨hc.1, hrun.2, ?_, ?_⟩
  · rw [hrun.1, hept]
  · rw [hrun.1]
    exact hcount.symm

end LogicLineages.OrdinalComparison
