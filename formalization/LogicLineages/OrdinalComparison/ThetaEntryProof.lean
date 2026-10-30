module
public import LogicLineages.OrdinalComparison.ThetaOrdinalProof
public import LogicLineages.OrdinalComparison.PhiResidueThreeProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem actualThetaEntryWitness : Targets.ActualThetaEntryWitness := by
  intro a ha hlimit
  dsimp only
  let v := actualOrdinalNorm a
  let u := Phi v
  let q := (u - 1) / 3
  let p := Ordinal.omega0 ^ Ordinal.omega0 * ((q - 1 : Nat) : Ordinal)
  have hTheta := actualThetaFacts
  have hnon : Ordinal.omega0 ≤ a := by
    have h : actualLimitPart a ≤ a := Ordinal.mul_div_le a Ordinal.omega0
    rw [hlimit] at h
    exact (Ordinal.omega0_le_of_isSuccLimit hTheta.2.1).trans h
  have hd := actualNonfiniteDecomposition a hnon ha
  have hv : 4 ≤ v := by
    have hn := hd.2.2.2
    rw [hlimit, hTheta.2.2] at hn
    dsimp only [v]
    omega
  have hres : Nat.ModEq 3 u 1 := actualPhiResidueThree v
  have hu : 4 ≤ u := hv.trans (self_lt_Phi v).le
  have hrem : u % 3 = 1 := by change u % 3 = 1 at hres; exact hres
  have hdiv : u = 3 * q + 1 := by dsimp [q]; omega
  have hq : 1 ≤ q := by omega
  have hstep : actualDescentStep a = Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) + 1 := by
    change actualMaximumPredecessor (actualLimitPart a) u = _
    rw [hlimit]
    exact actualThetaBudgetMaximum u hu hres
  have hcoeff : Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) =
      p + Ordinal.omega0 ^ Ordinal.omega0 := by
    change Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) =
      Ordinal.omega0 ^ Ordinal.omega0 * ((q - 1 : Nat) : Ordinal) + Ordinal.omega0 ^ Ordinal.omega0
    calc
      Ordinal.omega0 ^ Ordinal.omega0 * (q : Ordinal) =
          Ordinal.omega0 ^ Ordinal.omega0 * (((q - 1) + 1 : Nat) : Ordinal) :=
        congrArg (fun n : Nat => Ordinal.omega0 ^ Ordinal.omega0 * (n : Ordinal)) (by omega)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
  have hgroup : actualDescentStep a = p + (Ordinal.omega0 ^ Ordinal.omega0 + 1) := by
    rw [hstep, hcoeff, add_assoc]
  have hp := actualOmegaMultipleFacts (q - 1)
  have hpnorm : actualOrdinalNorm p = u - 4 := by
    rw [hp.2.1]
    omega
  have hnstep : actualOrdinalNorm (actualDescentStep a) = u := actualDescentStepNorm a hnon ha
  have hnsuffix : actualOrdinalNorm (Ordinal.omega0 ^ Ordinal.omega0 + 1) = 4 := by
    simpa only [Nat.cast_one, actualOmegaOmegaFacts.2.2] using
      (actualFiniteTailClosureNorm _ actualOmegaOmegaFacts.1 1).2
  exact ⟨hv, hres, hq, hstep, hgroup, hp.1, hpnorm, hp.2.2, hnstep, hnsuffix⟩

theorem fullActualThetaEntry : Targets.FullActualThetaEntry :=
  ⟨actualPhiResidueThree, actualOmegaMultipleFacts, actualThetaFacts,
    actualThetaBudgetMaximum, actualThetaEntryWitness⟩

end LogicLineages.OrdinalComparison
