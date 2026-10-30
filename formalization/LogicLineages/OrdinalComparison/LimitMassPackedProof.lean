module
public import LogicLineages.OrdinalComparison.LimitMassPackedTargets
public import LogicLineages.OrdinalComparison.LimitMassFirstProof
public import LogicLineages.OrdinalComparison.LimitMassNumericProof
public import LogicLineages.OrdinalComparison.AdjacentTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem limitmass_numeric_packing (R B c e w : Nat) (hce : c < e)
    (he : e ≤ B) (hR : R+1 ≤ B) (hw : w=B-e) :
    c+(R+1)*w ≤ Phi B ∧
    let k := Phi B-(c+(R+1)*w)
    k+(c+(R+1)*w)=Phi B ∧ (R+1)*w+k=Phi B-c ∧
    c+R*w+(w+k)=Phi B ∧ c+R*w ≤ (R+1)*B := by
  have hwe : w+e=B := by rw [hw]; exact Nat.sub_add_cancel he
  have hmul : (R+1)*w+(R+1)*e=(R+1)*B := by rw [← Nat.mul_add, hwe]
  have hce' : c ≤ (R+1)*e := hce.le.trans (Nat.le_mul_of_pos_left e (by omega))
  have hbound : c+(R+1)*w ≤ (R+1)*B := by omega
  have hsq := Nat.mul_le_mul_right B hR
  have hC := hsq.trans_lt (actualPhiSquareGap B)
  have hle := hbound.trans hC.le
  have hk := Nat.sub_add_cancel hle
  refine ⟨hle, hk, ?_, ?_, ?_⟩
  · omega
  · simp only [Nat.add_mul, Nat.one_mul] at hk ⊢
    omega
  · have hm := Nat.mul_le_mul_left R (Nat.sub_le B e)
    rw [← hw] at hm
    simp only [Nat.add_mul, Nat.one_mul]
    omega

private theorem limitmass_ordinal_packing (lo hi : Ordinal.{0})
    (hlo : Ordinal.omega0 ≤ lo) (hlt : lo < hi) (he : hi < epsilonZero)
    (hloP : ∃ d : Ordinal.{0}, 0 < d ∧ lo=Ordinal.omega0^d)
    (hhiP : ∃ d : Ordinal.{0}, 0 < d ∧ hi=Ordinal.omega0^d) (R k : Nat) :
    lo*(R : Ordinal)+(lo+(k : Ordinal)) = lo*((R+1 : Nat) : Ordinal)+(k : Ordinal) ∧
    lo*(R : Ordinal)+(lo+(k : Ordinal)) < hi ∧
    actualOrdinalNorm (lo*(R : Ordinal)+(lo+(k : Ordinal)))=(R+1)*actualOrdinalNorm lo+k := by
  have heq : lo*(R : Ordinal)+(lo+(k : Ordinal)) = lo*((R+1 : Nat) : Ordinal)+(k : Ordinal) := by
    rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]
  obtain ⟨d, hd, hld⟩ := hloP
  obtain ⟨f, hf, hhf⟩ := hhiP
  have hdf : d < f := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by rw [← hld, ← hhf]; exact hlt)
  have hsmall : lo*((R+1 : Nat) : Ordinal)+(k : Ordinal) < hi := by
    rw [hld, hhf]
    exact Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 (R+1))
      ((Ordinal.natCast_lt_omega0 k).trans_le (by rw [← hld]; exact hlo)) hdf
  have hpow : Ordinal.omega0^d < epsilonZero := by rw [← hld]; exact hlt.trans he
  have hpm := reserveStagePrincipalMultipleFacts d hpow (R+1)
  have htail := actualFiniteTailClosureNorm (Ordinal.omega0^d*((R+1 : Nat) : Ordinal)) hpm.1 k
  refine ⟨heq, heq.trans_lt hsmall, ?_⟩
  rw [heq, hld, htail.2, hpm.2]

theorem actualLimitMassPackedState : Targets.ActualLimitMassPackedState := by
  intro L beta hl hL E hv t c e hT hce he
  dsimp only
  let B := Phi t
  let C := Phi B
  let pe := actualMaximumPredecessor L.1.repr (B-e)
  let pc := actualMaximumPredecessor L.1.repr (B-c)
  let w := actualOrdinalNorm pe
  let R := profileReserveBlocks (profileBoundWord E)
  let p := c+R*w
  let k := C-(c+(R+1)*w)
  let r := pe+(k : Ordinal)
  let A := pe*(R : Ordinal)+r
  let Q := actualMaximumPredecessor pc (C-c)
  have hf := actualLimitMassFirstSuffixes L beta hl hL E hv t c e hT hce he
  have hR : R+4 ≤ t := (max_le_iff.mp (max_le_iff.mp hT).2).1
  have hB : t < B := self_lt_Phi t
  have heB : e ≤ B := ((Nat.le_add_right _ _).trans he).trans hB.le
  have hR' : R+1 ≤ B := by omega
  have hnum := limitmass_numeric_packing R B c e w hce heB hR' hf.2.2.2.1
  have hpcE : pc < epsilonZero := hf.2.2.1.trans (normalRepresentationSound L)
  have hshape := limitmass_ordinal_packing pe pc hf.1 hf.2.1 hpcE hf.2.2.2.2.2.2.2.1
    hf.2.2.2.2.2.2.2.2.1 R k
  have hAN : actualOrdinalNorm A=C-c := by rw [hshape.2.2]; exact hnum.2.2.1
  have hr := actualFiniteTailClosureNorm pe (hf.2.1.trans hpcE) k
  have htotal : p+actualOrdinalNorm r=C := by rw [hr.2]; exact hnum.2.2.2.1
  obtain ⟨d, hd, hpc⟩ := hf.2.2.2.2.2.2.2.2.1
  change pc=Ordinal.omega0^d at hpc
  have hlim : Order.IsSuccLimit pc := by
    rw [hpc]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hd)
  have hQN : actualOrdinalNorm Q=C-c := actualLimitMaximumPredecessorSaturation pc hpcE hlim _
  have hAQ : A ≤ Q := (actualMaximumPredecessor_correct pc hlim.bot_lt hpcE (C-c)).2 ⟨hshape.2.1, hAN.le⟩
  exact ⟨hnum.1, hnum.2.1, hshape.1, hshape.2.1, hAN, hQN, hAQ, htotal, hnum.2.2.2.2⟩

private theorem limitmass_limit_part (pi : Ordinal.{0}) (hl : Order.IsSuccLimit pi) : actualLimitPart pi=pi := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_div_cancel _ Ordinal.omega0_ne_zero]

private theorem limitmass_second_maximum (beta : Ordinal.{0}) (hb : 0 < beta)
    (he : Ordinal.omega0^beta < epsilonZero) (c t : Nat)
    (ht : c+actualOrdinalNorm (Ordinal.omega0^beta) ≤ t)
    (hpi : Order.IsSuccLimit (actualMaximumPredecessor (Ordinal.omega0^beta) (Phi t-c))) :
    let L := Ordinal.omega0^beta
    let pi := actualMaximumPredecessor L (Phi t-c)
    let Q := actualMaximumPredecessor pi (Phi (Phi t)-c)
    let g := compensatedPrefixControl c
    actualControlledStateAfter g (actualSuffixKernelInitial L c t) 2=Q ∧
    actualSuffixKernelCount L c t=actualControlledCount g Q+2 ∧
    actualSuffixKernel L c t=c+actualOrdinalNorm (actualControlledStateAfter g Q (actualControlledCount g Q)) := by
  dsimp only
  let L := Ordinal.omega0^beta
  let pi := actualMaximumPredecessor L (Phi t-c)
  let Q := actualMaximumPredecessor pi (Phi (Phi t)-c)
  let g := compensatedPrefixControl c
  have hfirst := actualSuffixKernelFirstMaximum beta hb he c t ht
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  have hpie := (actualMaximumPredecessor_correct L hlim.bot_lt he (Phi t-c)).1.1.trans he
  have hn : actualOrdinalNorm pi=Phi t-c := actualLimitMaximumPredecessorSaturation L he hlim _
  have htotal : c+actualOrdinalNorm pi=Phi t := by rw [hn]; have hh := self_lt_Phi t; omega
  have hstep : actualControlledStep g pi=Q := by
    change actualMaximumPredecessor (actualLimitPart pi) (Phi (c+actualOrdinalNorm pi)-c)=Q
    rw [limitmass_limit_part pi hpi, htotal]
  have hc := (actualControlledCountRecursion g pi hpie).2 (Ordinal.omega0_le_of_isSuccLimit hpi)
  rw [hstep] at hc
  have hcount : actualSuffixKernelCount L c t=actualControlledCount g Q+2 := by
    have hh := hfirst.2.1
    change actualSuffixKernelCount L c t=actualControlledCount g pi+1 at hh
    omega
  have hexit := actualControlledEndpointAlongTrace g pi hpie 1 (by omega)
  change actualControlledStateAfter g (actualControlledStep g pi)
    (actualControlledCount g (actualControlledStep g pi)) = actualControlledStateAfter g pi (actualControlledCount g pi) at hexit
  rw [hstep] at hexit
  refine ⟨?_, hcount, ?_⟩
  · change actualControlledStep g (actualControlledStateAfter g (actualSuffixKernelInitial L c t) 1)=Q
    rw [hfirst.1]
    exact hstep
  · have hh := hfirst.2.2
    change actualSuffixKernel L c t=c+actualOrdinalNorm (actualControlledStateAfter g pi (actualControlledCount g pi)) at hh
    rw [← hexit] at hh
    exact hh

theorem actualLimitMassSecondMaximum : Targets.ActualLimitMassSecondMaximum := by
  intro L beta hl hL E hv t c e hT hce he
  have hf := actualLimitMassFirstSuffixes L beta hl hL E hv t c e hT hce he
  obtain ⟨d, hd, hpc⟩ := hf.2.2.2.2.2.2.2.2.1
  have hlim : Order.IsSuccLimit (actualMaximumPredecessor L.1.repr (Phi t-c)) := by
    rw [hpc]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hd)
  have heps : Ordinal.omega0^beta < epsilonZero := by rw [← hL]; exact normalRepresentationSound L
  have hc : c+actualOrdinalNorm (Ordinal.omega0^beta) ≤ t := by rw [← hL]; omega
  have h := limitmass_second_maximum beta hl.bot_lt heps c t hc (by rw [← hL]; exact hlim)
  simpa only [← hL] using h

end LogicLineages.OrdinalComparison
