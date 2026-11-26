module
public import LogicLineages.PermittedControl.PureCertificateTerminalProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem shift_oriented_divergence (f : Nat → Nat) (mu nu P A A' : Ordinal.{0}) (i : Nat)
    (h : Targets.OrientedUnitDivergence f mu nu P ((descentWith f)^[i] A) ((descentWith f)^[i] A')) :
    OrientedUnitDivergence f mu nu P A A' := by
  obtain ⟨j,hj,hkeep,hkeep'⟩ := h
  refine ⟨i+j,?_,?_,?_⟩
  · simpa only [Nat.add_comm i j,Function.iterate_add_apply] using hj
  · simpa only [Nat.add_comm i j,Function.iterate_add_apply] using hkeep
  · simpa only [Nat.add_comm i j,Function.iterate_add_apply] using hkeep'

 theorem pure_successor_comparison (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu E beta A A' : Ordinal.{0}) (R t tau sigma : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hE : E < epsilonZero) (hb : beta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hb2 : 2 ≤ beta) (hbE : beta < E) (hR : 20 ≤ R) (hmuR : actualOrdinalNorm mu ≤ R)
    (hnuR : actualOrdinalNorm nu ≤ R) (hER : actualOrdinalNorm E ≤ R)
    (hbR : actualOrdinalNorm beta ≤ R) (hbsR : actualOrdinalNorm (beta+1) ≤ R)
    (ht : thickBlockTail R B ≤ t) (hp : actualLimitPart A=mu+Ordinal.omega0^E)
    (hp' : actualLimitPart A'=nu+Ordinal.omega0^E) (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hagree : ∀ e : Ordinal.{0}, beta < e → e < E → relativeProfile mu e=relativeProfile nu e)
    (hdiff : relativeProfile mu beta ≠ relativeProfile nu beta)
    (hHit : FirstEntry f A mu tau) (hHit' : FirstEntry f A' nu sigma) :
    compare (entryNormAt f A tau) (entryNormAt f A' sigma)=compare (relativeProfile nu beta) (relativeProfile mu beta) := by
  have hbs : beta+1 < epsilonZero := by simpa using (actualFiniteTailClosureNorm beta hb 1).1
  have hbsE : beta+1 ≤ E := Order.add_one_le_iff.mpr hbE
  have hbs1 : 1 ≤ beta+1 := by exact le_add_self
  obtain ⟨i,hi,hi',hiN,hiN'⟩ := actualProfileBandReturn f B hf mu nu E (beta+1) A A' R t
    hmu hnu hE hbs hA hA' hmud hnud hbs1 hbsE hR hmuR hnuR hER hbsR ht hp hp' hn hn'
    (by intro e he heE; exact hagree e ((Order.add_one_le_iff).mp he) heE)
  have hgrow := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
  have hlarge := sensitive_tail_large R B t ht
  have hhead := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (by
    exact (Ordinal.zero_lt_one.trans_le hbs1).ne')
  have hlim := (interval_iff_limitPart _ (mu+Ordinal.omega0^(beta+1)) (Or.inr (Ordinal.isSuccLimit_add mu hhead))).mp ⟨hi.1,hi.2.1⟩
  have hlim' := (interval_iff_limitPart _ (nu+Ordinal.omega0^(beta+1)) (Or.inr (Ordinal.isSuccLimit_add nu hhead))).mp ⟨hi'.1,hi'.2.1⟩
  have hPw : Ordinal.omega0 ≤ Ordinal.omega0^beta := Ordinal.left_le_opow _ (by
    exact ((by norm_num : (0 : Ordinal) < 2).trans_le hb2))
  rcases lt_or_gt_of_ne hdiff with hlt | hgt
  · have hdiv := actualPureSuccessorSeparation f B hf mu nu beta _ _ R (f^[i] t)
      hmu hnu hb (trajectory_below f A hA i) (trajectory_below f A' hA' i) hmud hnud hb2 hR hmuR hnuR hbR
      (ht.trans hgrow) hlim hlim' hiN hiN' hlt
    have ho := entry_order_from_oriented f B hf mu nu _ A A' t tau sigma hmu hnu hA hA' hmud hnud hPw
      hn hn' (by omega) (by omega) hHit hHit' (shift_oriented_divergence f mu nu _ A A' i hdiv)
    exact (compare_gt_iff_gt.mpr ho).trans (compare_gt_iff_gt.mpr hlt).symm
  · have hdiv := actualPureSuccessorSeparation f B hf nu mu beta _ _ R (f^[i] t)
      hnu hmu hb (trajectory_below f A' hA' i) (trajectory_below f A hA i) hnud hmud hb2 hR hnuR hmuR hbR
      (ht.trans hgrow) hlim' hlim hiN' hiN hgt
    have ho := entry_order_from_oriented f B hf nu mu _ A' A t sigma tau hnu hmu hA' hA hnud hmud hPw
      hn' hn (by omega) (by omega) hHit' hHit (shift_oriented_divergence f nu mu _ A' A i hdiv)
    exact (compare_lt_iff_lt.mpr ho).trans (compare_lt_iff_lt.mpr hgt).symm

end LogicLineages.PermittedControl
