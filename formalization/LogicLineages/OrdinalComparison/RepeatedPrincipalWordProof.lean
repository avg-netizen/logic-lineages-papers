module
public import LogicLineages.OrdinalComparison.RepeatedPrincipalWordTargets
public import LogicLineages.OrdinalComparison.PrincipalWordActionProof
public import LogicLineages.OrdinalComparison.PrincipalKernelWordProof
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof
public import LogicLineages.OrdinalComparison.ReserveStageProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem repeated_principal_weight (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+Vendor.R1.treeWeight eta.1 := by
  have h := (actualCNFBlock eta.1.repr 0 (normalRepresentationSound eta)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) 1).2.1
  have hz : actualOrdinalNorm (0 : Ordinal)=0 := actualOrdinalNorm_notationCorrespondence (0 : NONote)
  simpa only [PNat.one_coe, Nat.cast_one, mul_one, add_zero, Nat.one_mul, hz,
    Nat.add_zero, actualOrdinalNorm_notationCorrespondence eta] using h

theorem actualRepeatedPrincipalWordPositions : Targets.ActualRepeatedPrincipalWordPositions := by
  intro eta heta q c
  dsimp only
  rw [actualPrincipalKernelWordPositions, List.map_reverse]
  apply congrArg List.reverse
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hiq : i < q := by simpa using hi
    simp [principalBlocksWeight, List.take_replicate, Nat.min_eq_left hiq.le,
      repeated_principal_weight eta, nsmul_eq_mul]

theorem actualRepeatedPrincipalWordRun : Targets.ActualRepeatedPrincipalWordRun := by
  intro eta heta q c n
  dsimp only
  let theta := Ordinal.omega0^eta.1.repr
  let w := actualOrdinalNorm theta
  let initial := theta*(q : Ordinal)+(n : Ordinal)
  let g := compensatedPrefixControl c
  let C := actualControlledCount g initial
  let t := c+q*w+n
  have hdom : GenuinePrincipalBlocks (List.replicate q eta.1) := by
    constructor
    · intro e he
      have heq := List.eq_of_mem_replicate he
      subst e
      exact ⟨eta.2, heta⟩
    · simp
  have hsum : principalBlockSum (List.replicate q eta.1)=theta*(q : Ordinal) := by
    simp [principalBlockSum, List.sum_replicate, Ordinal.nsmul_eq_mul, theta]
  have hweight : principalBlocksWeight (List.replicate q eta.1)=q*w := by
    simp [principalBlocksWeight, List.sum_replicate, nsmul_eq_mul, w, theta, repeated_principal_weight eta]
  have hcorrect := actualPrincipalWordRunCorrect (List.replicate q eta.1) hdom c n
  have hgood := actualPrincipalWordInputsGenuine (List.replicate q eta.1) hdom c n
  dsimp only at hcorrect
  rw [hsum, hweight] at hcorrect
  rw [hweight] at hgood
  have heps : theta < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr (normalRepresentationSound eta)
  have hpm := reserveStagePrincipalMultipleFacts eta.1.repr heps q
  have htail := actualFiniteTailClosureNorm (theta*(q : Ordinal)) hpm.1 n
  have htotal : c+actualOrdinalNorm initial=t := by
    change c+actualOrdinalNorm (theta*(q : Ordinal)+(n : Ordinal))=t
    rw [htail.2, hpm.2]
    simp only [t, w, theta, Nat.add_assoc]
  have hn := actualControlledNormIteration g initial htail.1 C le_rfl
  have hiter := reserveCompensatedIteration c (actualOrdinalNorm initial) C
  rw [htotal] at hiter
  have hexit : c+actualOrdinalNorm (actualControlledStateAfter g initial C)=(Phi^[C]) t := by
    rw [hn]
    exact hiter
  refine ⟨?_, hgood⟩
  change actualPrincipalWordRun (principalKernelWord (List.replicate q eta.1) c) t =
    (c+actualOrdinalNorm (actualControlledStateAfter g initial C), C)
  rw [hexit]
  exact hcorrect

end LogicLineages.OrdinalComparison
