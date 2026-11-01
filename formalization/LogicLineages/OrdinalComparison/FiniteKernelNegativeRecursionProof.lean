module
public import LogicLineages.OrdinalComparison.FiniteKernelNegativeRecursionTargets
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FiniteKernelNegativeRecursion

theorem counterexample : Targets.ActualNegativeFiniteKernelRecursionCounterexample := by
  intro c t ht
  dsimp only
  let entry := actualSuffixKernel (Ordinal.omega0 ^ (2 : Ordinal)) (c+2) t
  let E := actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) (c+2) t
  have hentry : t ≤ entry := iterate_self_le (fun x => (self_lt_Phi x).le) _ t
  have hbase : 1 < E :=
    SignedKernelDomainProof.finiteDegreeCounterLowerBound.2 2 (c+2) 1 t le_rfl
      (max_le (by omega) (by omega))
  have hc := (FiniteKernelRecursion.block 0 c t (by omega)).1
  simp only [Nat.zero_add,Nat.cast_ofNat,Nat.add_zero] at hc
  simp only [Nat.cast_one,Ordinal.opow_one] at hc
  have hchildcount := (actualOmegaSuffixKernel c entry (by omega)).1
  have hcount : actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t = E+1 := by
    change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) c t =
      actualSuffixKernelCount Ordinal.omega0 c entry+E at hc
    simpa only [Ordinal.opow_one,hchildcount,Nat.add_comm] using hc
  have hchild : signedKernelDepth 1 c (-2) entry = -1 := by
    have h := (SignedKernelDomainProof.degreeOneSignedDomain c entry (by omega) (-2)).1
    simpa using h
  have hpositive : 0 < signedKernelDepth 2 c (-2) t := by
    dsimp only [signedKernelDepth]
    simp only [Nat.cast_ofNat]
    rw [hcount]
    omega
  refine ⟨hpositive,hchild,?_⟩
  have hleft : rawSignedKernelValue 2 c (-2) t = (Phi^[E-1]) t := by
    have hdepth : (signedKernelDepth 2 c (-2) t).toNat = E-1 := by
      dsimp only [signedKernelDepth]
      simp only [Nat.cast_ofNat]
      rw [hcount]
      omega
    simp only [rawSignedKernelValue,hdepth]
  have hright : rawSignedKernelValue 1 c (-2) entry = entry := by
    simp only [rawSignedKernelValue,hchild]
    rfl
  rw [hleft,hright]
  change (Phi^[E-1]) t < (Phi^[E]) t
  have hE : E=(E-1)+1 := by omega
  calc
    _ < Phi ((Phi^[E-1]) t) := self_lt_Phi _
    _ = (Phi^[E]) t := by
      conv_rhs => rw [hE,Function.iterate_succ_apply']

end LogicLineages.OrdinalComparison.FiniteKernelNegativeRecursion
