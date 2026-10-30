module
public import LogicLineages.OrdinalComparison.AdjacentPackedTargets
public import LogicLineages.OrdinalComparison.AffordableLeadingProof
public import LogicLineages.OrdinalComparison.ProfileDirectPackedProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualAdjacentLeadingCoverage : Targets.ActualAdjacentLeadingCoverage := by
  intro L hp hlarge E hv t e hT he
  dsimp only
  have hfour : 4 ≤ t := (max_le_iff.mp hT).1
  have hH : profileReserveLeadingBound (profileBoundWord E) ≤ t :=
    (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hT).2).2).2).2
  have hg := reserveStageTwoMulLtPhi t
  have hbudget : t ≤ Phi t-e := by omega
  have hb : 2 ≤ Phi t-e := by omega
  have hf := actualAffordableLeadingMaximum L hp hlarge (Phi t-e) hb
  refine ⟨hb, hf.2.2.2.1, hf.2.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.1.trans (Nat.sub_le _ _), hf.2.2.2.2.2.2.2.2.1, ?_⟩
  intro rho hr
  have hw := actualProfileBoundCompiler L.1.repr hlarge E hv
  have hh := hw.2.1 rho hr
  obtain ⟨delta, hd, hdelta, hle, _, hnorm⟩ := actualProfileLeadingMonomialCorrect rho hh.1
  have hN : actualOrdinalNorm (actualProfileLeadingMonomial rho) ≤ Phi t-e := by
    rw [hnorm]
    have hm : profileLeadingWeight rho ≤ profileReserveLeadingBound (profileBoundWord E) :=
      List.le_max_of_le' 0 (List.mem_map.mpr ⟨rho, hr, rfl⟩) le_rfl
    exact hm.trans (hH.trans hbudget)
  rw [hdelta] at hN ⊢
  exact hf.2.2.2.2.2.2.2.2.2 delta (by rw [← hdelta]; exact hle.trans_lt hh.2) hN

private theorem adjacent_product_budget (R t : Nat) (hR : R+5 ≤ t) :
    (R+2) * Phi t < Phi (t+1) := by
  let B := Phi t
  have hB : t < B := self_lt_Phi t
  have hpos : 0 < B := by omega
  have ht : B < 2^B := Nat.lt_two_pow_self
  have hsq : B*B < 2^B*2^B :=
    (Nat.mul_lt_mul_of_pos_left ht hpos).trans_le (Nat.mul_le_mul_right _ ht.le)
  rw [← Nat.pow_add] at hsq
  have he : B+B ≤ 2^(B+1) := by rw [Nat.pow_succ]; omega
  have hh := hsq.trans_le (Nat.pow_le_pow_right (by decide) he)
  exact (Nat.mul_le_mul_right B (by omega : R+2 ≤ B)).trans_lt (hh.trans_le (Phi_succ_gap t))

private theorem adjacent_ordinal_packing (L pi b : Ordinal.{0})
    (he : L < epsilonZero) (hp : ∃ ell : Ordinal.{0}, L = Ordinal.omega0 ^ ell)
    (hpiomega : Ordinal.omega0 ≤ pi) (hpiL : pi < L)
    (hpower : ∃ gamma : Ordinal.{0}, 0 < gamma ∧ pi = Ordinal.omega0 ^ gamma)
    (hbL : b < L) (hbsmall : b < pi*Ordinal.omega0) (R k : Nat) :
    pi*(R : Ordinal)+(b+(k : Ordinal)) < L ∧
    actualOrdinalNorm (pi*(R : Ordinal)+(b+(k : Ordinal))) =
      R*actualOrdinalNorm pi+actualOrdinalNorm b+k := by
  obtain ⟨gamma, hg, hpi⟩ := hpower
  have hpieps : Ordinal.omega0 ^ gamma < epsilonZero := by rw [← hpi]; exact hpiL.trans he
  have hpm := reserveStagePrincipalMultipleFacts gamma hpieps R
  rw [← hpi] at hpm
  have htail := actualFiniteTailClosureNorm b (hbL.trans he) k
  have hrbound : b+(k : Ordinal) < Ordinal.omega0^(gamma+1) := by
    have hb' : b < Ordinal.omega0^(gamma+1) := by rw [Ordinal.opow_add_one, ← hpi]; exact hbsmall
    have hk' : (k : Ordinal) < Ordinal.omega0^(gamma+1) :=
      (Ordinal.natCast_lt_omega0 k).trans_le (by
        simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
          (show (1 : Ordinal) ≤ gamma+1 from le_add_self))
    exact Ordinal.isPrincipal_add_omega0_opow (gamma+1) hb' hk'
  have hAn := actualDivisiblePrefixNormAddition (pi*(R : Ordinal)) (b+(k : Ordinal)) hpm.1 htail.1
    gamma (by rw [← hpi]; exact ⟨(R : Ordinal), rfl⟩) hrbound
  obtain ⟨ell, hL⟩ := hp
  have hge : gamma < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [← hpi, ← hL]; exact hpiL)
  constructor
  · have hprefix : pi*(R : Ordinal) < Ordinal.omega0^(gamma+1) := by
      rw [Ordinal.opow_add_one, ← hpi]
      exact (mul_lt_mul_iff_right₀ (Ordinal.omega0_pos.trans_le hpiomega)).mpr (Ordinal.natCast_lt_omega0 R)
    have ha := Ordinal.isPrincipal_add_omega0_opow (gamma+1) hprefix hrbound
    apply ha.trans_le
    rw [hL]
    exact Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.add_one_le_iff.mpr hge)
  · rw [hAn.2, hpm.2, htail.2, Nat.add_assoc]

private theorem adjacent_numeric_packing (R t c e w : Nat) (hR : R+5 ≤ t)
    (hc : c ≤ t+1) (he : e ≤ t) (hw : w ≤ Phi t) :
    let B := Phi t
    let B' := Phi (t+1)
    let p := c+R*w
    let k := (B'+e)-(B+p)
    B+p ≤ B'+e ∧ k+(B+p)=B'+e ∧ p ≤ (R+1)*B ∧
    e+(B-e)=B ∧ p+(B-e+k)=B' ∧ R*w+(B-e)+k=B'-c := by
  dsimp only
  have hB := self_lt_Phi t
  have hp : c+R*w ≤ (R+1)*Phi t := by
    have hm := Nat.mul_le_mul_left R hw
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hgap := adjacent_product_budget R t hR
  have hnontrunc : Phi t+(c+R*w) ≤ Phi (t+1)+e := by
    have hh : Phi t+(c+R*w) ≤ (R+2)*Phi t := by
      simp only [Nat.add_mul, Nat.one_mul] at hp ⊢
      omega
    exact (hh.trans_lt hgap).le.trans (Nat.le_add_right _ _)
  have hk := Nat.sub_add_cancel hnontrunc
  refine ⟨hnontrunc, hk, hp, ?_, ?_, ?_⟩ <;> omega

-- Root-scoped 400k elaboration allowance after receipt 1793352492297872375-6;
-- all native memory/CPU/RSS/thread guards remain unchanged.
set_option maxHeartbeats 400000 in
theorem actualAdjacentPackedState : Targets.ActualAdjacentPackedState := by
  intro L hp hlarge E hv t c e hT hc he
  dsimp only
  let B := Phi t
  let B' := Phi (t+1)
  let b := actualMaximumPredecessor L.1.repr (B-e)
  let pi := (profileLeadingNote (maximumPredecessor L (B-e))).1.repr
  let R := profileReserveBlocks (profileBoundWord E)
  let w := actualOrdinalNorm pi
  let p := c+R*w
  let k := (B'+e)-(B+p)
  let A := pi*(R : Ordinal)+(b+(k : Ordinal))
  let Q := actualMaximumPredecessor L.1.repr (B'-c)
  have hlead := actualAdjacentLeadingCoverage L hp hlarge E hv t e hT he
  have hf := actualAffordableLeadingMaximum L hp hlarge (B-e) hlead.1
  have hR : R+5 ≤ t := (max_le_iff.mp (max_le_iff.mp hT).2).1
  have hnum := adjacent_numeric_packing R t c e w hR
    ((Nat.le_add_right _ _).trans hc) ((Nat.le_add_right _ _).trans he) hlead.2.2.2.1
  have hnontrunc : B+p ≤ B'+e := hnum.1
  have hk : k+(B+p)=B'+e := hnum.2.1
  have hpB : p ≤ (R+1)*B := hnum.2.2.1
  have hbN : actualOrdinalNorm b = B-e := hf.2.1
  have heB : e+actualOrdinalNorm b=B := by rw [hbN]; exact hnum.2.2.2.1
  have hbsmall : b < pi*Ordinal.omega0 := hf.2.2.2.2.2.1
  have hbL : b < L.1.repr :=
    (actualMaximumPredecessor_correct L.1.repr (Ordinal.omega0_pos.trans hlarge)
      (normalRepresentationSound L) (B-e)).1.1
  have htail := actualFiniteTailClosureNorm b (hbL.trans (normalRepresentationSound L)) k
  have htotal : p+actualOrdinalNorm (b+(k : Ordinal))=B' := by
    rw [htail.2, hbN]
    exact hnum.2.2.2.2.1
  have hpack := adjacent_ordinal_packing L.1.repr pi b (normalRepresentationSound L) hp
    hlead.2.1 hlead.2.2.1 hlead.2.2.2.2.1 hbL hbsmall R k
  have hsmall : A < L.1.repr := hpack.1
  have hAN : actualOrdinalNorm A=B'-c := by
    change actualOrdinalNorm (pi*(R : Ordinal)+(b+(k : Ordinal)))=B'-c
    rw [hpack.2, hbN]
    exact hnum.2.2.2.2.2
  obtain ⟨ell, hL⟩ := hp
  have hell : (1 : Ordinal) < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [Ordinal.opow_one, ← hL]; exact hlarge)
  have hlim : Order.IsSuccLimit L.1.repr := by
    rw [hL]
    exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt (zero_lt_one.trans hell))
  have hQn : actualOrdinalNorm Q=B'-c := actualLimitMaximumPredecessorSaturation _ (normalRepresentationSound L) hlim _
  have hAQ : A ≤ Q := (actualMaximumPredecessor_correct _ hlim.bot_lt (normalRepresentationSound L) (B'-c)).2
    ⟨hsmall, hAN.le⟩
  exact ⟨hnontrunc, hk, hpB, hbsmall, hsmall, hbN, heB, htotal, hAN, hAQ, hQn⟩

end LogicLineages.OrdinalComparison
