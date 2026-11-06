module
public import LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeEqualityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Proof
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion
open KernelSourceCompletion.UniformCompletion.Proof

/-- Reuse the unchanged published threshold; every later input pays the
cross-pair region as well as the already built-in self-pair budgets. -/
theorem tail_region (d c e : Nat) (j k : Int) (t : Nat)
    (ht : equalityTail d c e j k ≤ t) : region d c e j k 0 t := by
  simp only [equalityTail,max_le_iff] at ht
  refine ⟨ht.1,?_⟩
  simpa only [Nat.add_zero] using ht.2.1.trans (self_lt_Phi t).le

theorem region_swap (d c e : Nat) (j k : Int) (t : Nat)
    (hr : region d c e j k 0 t) : region d e c k j 0 t := by
  refine ⟨hr.1,?_⟩
  have heq : e+c+k.natAbs+j.natAbs+0+1 =
      c+e+j.natAbs+k.natAbs+0+1 := by omega
  change degreeConstant d * (e+c+k.natAbs+j.natAbs+0+1) ≤ Phi t
  rw [heq]
  exact hr.2

theorem signed_input_mono (d c : Nat) (j : Int) (t u : Nat)
    (hd : 1 ≤ d) (htu : t ≤ u) (hc : c ≤ Phi t) :
    sourceSignedValue d c j t ≤ sourceSignedValue d c j u := by
  have hcount := (Focused.sourceInputMassOrder d c c t u hd le_rfl htu hc).2.1
  have hdepth : (sourceSignedDepth d c j t).toNat ≤
      (sourceSignedDepth d c j u).toNat := by
    unfold sourceSignedDepth
    omega
  change (Phi^[(sourceSignedDepth d c j t).toNat]) t ≤
    (Phi^[(sourceSignedDepth d c j u).toNat]) u
  exact ((Phi_strictMono.iterate (sourceSignedDepth d c j t).toNat).monotone htu).trans
    (iterate_index_mono (fun x => (self_lt_Phi x).le) u hdepth)

theorem strict_inputs (d c e : Nat) (j k : Int) (t u : Nat)
    (hd : 3 ≤ d) (hr : region d c e j k 0 t) (htu : t < u) :
    sourceSignedValue d e k t < sourceSignedValue d c j u := by
  have hs := (quantitativeSeparation d c e j k 0 t hd hr).1
  change sourceSignedValue d e k t < sourceSignedValue d c j (t+1) at hs
  have hmass := (Focused.broadUnsignedBlockCut.1 d c e j k 0 t hd hr).1
  have hnext : Phi t ≤ Phi (t+1) := Phi_strictMono.monotone (Nat.le_succ t)
  have hc : c ≤ Phi (t+1) := by omega
  exact hs.trans_le (signed_input_mono d c j (t+1) u (by omega)
    (Nat.succ_le_of_lt htu) hc)

theorem kernelOrderCorrect : Targets.KernelOrderCorrect := by
  intro d c e j k hd t u ht hu
  have hrt := tail_region d c e j k t ht
  have hru := tail_region d c e j k u hu
  have hdomains := effectiveEqualityTail d c e j k hd t u ht hu
  rcases lt_trichotomy t u with htu | rfl | hut
  · have hs := strict_inputs d e c k j t u hd
      (region_swap d c e j k t hrt) htu
    exact ⟨fun _ => Or.inl htu,fun _ => hs⟩
  · rcases lt_trichotomy c e with hce | rfl | hec
    · have hs := (quantitativeSeparation d c e j k 0 t hd hrt).2 hce
      change sourceSignedValue d e k t < sourceSignedValue d c j t at hs
      constructor
      · intro h; exact False.elim ((not_lt_of_gt hs) h)
      · intro h
        simp only [KernelLexLT,lt_self_iff_false,true_and,false_or] at h
        omega
    · have ho := (Focused.exactSignedOrder d c t hd hdomains.1 j k
        hdomains.2.2.1 hdomains.2.2.2.1).1
      simpa only [KernelLexLT,lt_self_iff_false,true_and,false_or] using ho
    · have hs := (quantitativeSeparation d e c k j 0 t hd
        (region_swap d c e j k t hrt)).2 hec
      change sourceSignedValue d c j t < sourceSignedValue d e k t at hs
      exact ⟨fun _ => Or.inr ⟨rfl,Or.inl hec⟩,fun _ => hs⟩
  · have hs := strict_inputs d c e j k u t hd hru hut
    constructor
    · intro h; exact False.elim ((not_lt_of_gt hs) h)
    · intro h
      simp only [KernelLexLT] at h
      omega

end LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Proof
