module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeBudgetProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeCubicProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof

theorem degreeConstant_mono : Monotone degreeConstant := by
  intro a b hab
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hab) hab

theorem degreeThreshold_mono : Monotone degreeThreshold := by
  apply monotone_nat_of_le_succ
  intro d
  by_cases h : d+1 ≤ 3
  · have hd : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hd with rfl | rfl | rfl <;> decide
  · rw [degreeThreshold,if_neg h]
    exact Nat.le_max_left _ _

theorem unsignedSeparation : Targets.UnsignedSeparation := by
  intro d c e R t hd
  induction d, hd using Nat.le_induction generalizing c e R t with
  | base =>
    intro hr
    apply cubicUnsignedSeparation c e R t hr.1
    simpa only [region,degreeConstant,Int.natAbs_zero,Nat.add_zero] using hr.2
  | succ d hd ih =>
    intro hr
    have hdp : 1 ≤ d := by omega
    have hparent : 3 ≤ d+1 := by omega
    have hbounds := Focused.broadUnsignedBlockCut.1 (d+1) c e 0 0 R t hparent hr
    have hc : c+(d+1) ≤ Phi t := by omega
    have he : e+(d+1) ≤ Phi t := by omega
    let Ue := sourceValue (d+1) (e+(d+1)) t
    let Uc := sourceValue (d+1) (c+(d+1)) t
    let Vc := sourceValue (d+1) (c+(d+1)) (t+1)
    have hBUe : Phi t ≤ Ue := source_value_lower (d+1) (e+(d+1)) t (by omega) he
    have htUe : t ≤ Ue := (self_lt_Phi t).le.trans hBUe
    have hsmall : region d c e 0 0 R Ue := by
      constructor
      · exact (degreeThreshold_mono (Nat.le_succ d)).trans (hr.1.trans htUe)
      · exact (Nat.mul_le_mul_right _ (degreeConstant_mono (Nat.le_succ d))).trans
          (hr.2.trans (Phi_strictMono.monotone htUe))
    have hinner := ih c e R Ue hsmall
    have hec : sourceValue (d+1) e t = sourceValue d e Ue := by
      simpa only [Nat.add_sub_cancel] using source_block (d+1) e t (by omega) he
    have hcc : sourceValue (d+1) c t = sourceValue d c Uc := by
      simpa only [Nat.add_sub_cancel] using source_block (d+1) c t (by omega) hc
    have hcv : sourceValue (d+1) c (t+1) = sourceValue d c Vc := by
      simpa only [Nat.add_sub_cancel] using source_block (d+1) c (t+1) (by omega)
        (hc.trans (Phi_strictMono.monotone (Nat.le_succ t)))
    have hcUe : c ≤ Phi Ue := by
      have hs := self_lt_Phi Ue
      omega
    constructor
    · have hUV : Ue < Vc := source_cross_value (d+1) (c+(d+1)) (e+(d+1)) t hc
      have hm := Focused.sourceInputMassOrder d c c (Ue+1) Vc hdp le_rfl
        (Nat.succ_le_of_lt hUV)
        (hcUe.trans (Phi_strictMono.monotone (Nat.le_succ Ue)))
      rw [hec,hcv]
      exact hinner.1.trans_le hm.2.2.1
    · intro hce
      have hmass := Focused.sourceInputMassOrder (d+1) (c+(d+1)) (e+(d+1)) t t
        (by omega) (by omega) le_rfl he
      have hUU : Ue ≤ Uc := hmass.2.2.1
      have hm := Focused.sourceInputMassOrder d c c Ue Uc hdp le_rfl hUU hcUe
      rw [hec,hcc]
      exact (hinner.2 hce).trans_le hm.2.2.1

/-- Removing a negative signed offset costs at most its absolute value in
forward iterations. The proof uses only order, not an inverse of Phi. -/
theorem signed_transport (d c e : Nat) (j k : Int) (R t u : Nat)
    (h : (Phi^[R+j.natAbs+k.natAbs]) (sourceValue d e t) < sourceValue d c u) :
    (Phi^[R]) (sourceSignedValue d e k t) < sourceSignedValue d c j u := by
  have hj : -(j.natAbs : Int) ≤ j := by omega
  have hk : k ≤ (k.natAbs : Int) := Int.le_natAbs
  have hc : sourceCount d c u ≤ j.natAbs+(sourceSignedDepth d c j u).toNat := by
    unfold sourceSignedDepth
    omega
  have he : (sourceSignedDepth d e k t).toNat ≤ sourceCount d e t+k.natAbs := by
    unfold sourceSignedDepth
    omega
  have hleft :
      (Phi^[j.natAbs]) ((Phi^[R]) (sourceSignedValue d e k t)) ≤
        (Phi^[R+j.natAbs+k.natAbs]) (sourceValue d e t) := by
    unfold sourceSignedValue sourceValue
    rw [← Function.iterate_add_apply,← Function.iterate_add_apply,
      ← Function.iterate_add_apply]
    exact iterate_index_mono (fun x => (self_lt_Phi x).le) t (by omega)
  have hright : sourceValue d c u ≤ (Phi^[j.natAbs]) (sourceSignedValue d c j u) := by
    unfold sourceSignedValue sourceValue
    rw [← Function.iterate_add_apply]
    exact iterate_index_mono (fun x => (self_lt_Phi x).le) u hc
  exact (Phi_strictMono.iterate j.natAbs).lt_iff_lt.mp
    ((hleft.trans_lt h).trans_le hright)

theorem quantitativeSeparation : Targets.QuantitativeSeparation := by
  intro d c e j k R t hd hr
  have hreg : region d c e 0 0 (R+j.natAbs+k.natAbs) t := by
    refine ⟨hr.1,?_⟩
    have heq : c+e+(0 : Int).natAbs+(0 : Int).natAbs+(R+j.natAbs+k.natAbs)+1 =
        c+e+j.natAbs+k.natAbs+R+1 := by simp only [Int.natAbs_zero]; omega
    rw [heq]
    exact hr.2
  have hu := unsignedSeparation d c e (R+j.natAbs+k.natAbs) t hd hreg
  exact ⟨signed_transport d c e j k R t (t+1) hu.1,
    fun hce => signed_transport d c e j k R t t (hu.2 hce)⟩

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof
