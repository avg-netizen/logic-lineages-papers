module
public import LogicLineages.PermittedControl.SensitiveSetupProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem sensitive_admission (f : Nat → Nat) (B : Nat) (mu nu P a r A A' : Ordinal.{0}) (R t : Nat)
    (hs : Targets.SensitiveUnitSetup f B mu nu P a r A A' R t) :
    Targets.OrientedUnitDivergence f mu nu P A A' ∨
    ∃ i : Nat, FirstEntry f A (mu+(P+Ordinal.omega0^a)) i ∧
      FirstEntry f A' (nu+(P+Ordinal.omega0^a)) i ∧
      Targets.SensitiveUnitSetup f B mu nu P a 0 ((descentWith f)^[i] A)
        ((descentWith f)^[i] A') R (f^[i] t) := by
  have hs0 := hs
  rcases hs with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hdiv,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hnorm,hnorm',hcd⟩
  have hap : 0 < a := lt_of_lt_of_le (by norm_num) h2
  let rho := P+Ordinal.omega0^a
  let sigma := rho+r
  have hrho := epsilonZero_add_principal hP (phase_power_below a ha)
  have hsigma := epsilonZero_add_principal hrho (hr.trans (phase_power_below a ha))
  have hrhol : Order.IsSuccLimit rho := Ordinal.isSuccLimit_add P
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hap.ne')
  have hsigmal : Order.IsSuccLimit sigma := unit_gap_limit P a r hap hrd
  have hu := unit_state_initial mu P a r A t hmu hP ha hPpos hap hdiv hr hrd hA hpart hnorm
  have hv := unit_state_initial nu P a r A' t hnu hP ha hPpos hap hdiv hr hrd hA' hpart' hnorm'
  have ht2 : 2 ≤ t := by have h := sensitive_tail_large R B t ht; omega
  obtain ⟨i,j,hi,hj,hEi,hEj,hguard,hguard',hreset,hdiverge⟩ := synchronizedTargetVisits f B hf
    mu nu sigma rho t hmu hnu hsigma hrho hmud hnud hsigmal hrhol le_self_add
    (max_le ht2 (max_le hu.2.1 (max_le hv.2.1 (max_le hu.2.2.1 hv.2.2.1))))
  rw [← hu.1] at hi hEi
  rw [← hv.1] at hj hEj
  by_cases hij : i=j
  · subst j
    right
    refine ⟨i,hi,hj,?_⟩
    have hEt := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
    have hparti := (interval_iff_limitPart _ _ (Or.inr (Ordinal.isSuccLimit_add mu hrhol))).mp ⟨hi.1,hi.2.1⟩
    have hpartj := (interval_iff_limitPart _ _ (Or.inr (Ordinal.isSuccLimit_add nu hrhol))).mp ⟨hj.1,hj.2.1⟩
    refine ⟨hf,hmu,hnu,hP,ha,trajectory_below f A hA i,trajectory_below f A' hA' i,hmud,hnud,
      hPpos,h2,hdiv,Ordinal.opow_pos a Ordinal.omega0_pos,Or.inl rfl,hR,hmuR,hnuR,hPR,haR,
      ht.trans hEt,?_,?_,hEi,hEj,hcd⟩
    · simpa only [add_zero] using hparti
    · simpa only [add_zero] using hpartj
  · left
    apply sensitive_orient f B mu nu P a r A A' R t hs0
    obtain ⟨h,hh,hne,hlo,hlo'⟩ := hdiverge hij
    have hPr : P ≤ rho := le_self_add
    have hAn : A=countInitial (mu+sigma) t := hu.1
    have hAn' : A'=countInitial (nu+sigma) t := hv.1
    simp only [relativeState] at hne hlo hlo'
    rw [← hAn,← hAn'] at hne
    rw [← hAn] at hlo
    rw [← hAn'] at hlo'
    exact ⟨h,hne,hPr.trans hlo,hPr.trans hlo'⟩

 theorem retained_prefix_limit (P a : Ordinal.{0}) (hP : 0 < P) (ha : 0 < a)
    (hd : Ordinal.omega0^a ∣ P) : Order.IsSuccLimit P := by
  obtain ⟨q,hq⟩ := hd
  have hqn : q ≠ 0 := by intro h; rw [h,mul_zero] at hq; exact hP.ne' hq
  rw [hq]
  exact Ordinal.isSuccLimit_mul_left
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 ha.ne') (pos_iff_ne_zero.mpr hqn)

/-- Concrete next relative state and norm at an actual admitted top. -/
 theorem sensitive_top_step (f : Nat → Nat) (B : Nat) (mu nu P a A A' : Ordinal.{0}) (R t : Nat)
    (hs : Targets.SensitiveUnitSetup f B mu nu P a 0 A A' R t) :
    descentWith f A-mu = P+actualMaximumPredecessor (Ordinal.omega0^a)
      (f t-relativeProfile mu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P) ∧
    descentWith f A'-nu = P+actualMaximumPredecessor (Ordinal.omega0^a)
      (f t-relativeProfile nu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P) ∧
    actualOrdinalNorm (descentWith f A)=f t ∧ actualOrdinalNorm (descentWith f A')=f t ∧
    P ≤ actualLimitPart (descentWith f A-mu) ∧ P ≤ actualLimitPart (descentWith f A'-nu) := by
  rcases hs with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hdiv,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hnorm,hnorm',hcd⟩
  have hap : 0 < a := lt_of_lt_of_le (by norm_num) h2
  have hPl := retained_prefix_limit P a hPpos hap hdiv
  have hPt : actualLimitPart P=P := by simpa using limitPart_tail P hPl 0
  have hlarge := sensitive_tail_large R B t ht
  have hu := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  have hc := (relativePrefixNorm mu (Ordinal.log Ordinal.omega0 P) hmu).2.2.trans hmuR
  have hd := (relativePrefixNorm nu (Ordinal.log Ordinal.omega0 P) hnu).2.2.trans hnuR
  have hm := retainedLocalPhase mu P a (f t) hmu hP ha hPpos hap hdiv (by omega) (by omega)
  have hn := retainedLocalPhase nu P a (f t) hnu hP ha hPpos hap hdiv (by omega) (by omega)
  have hm' : descentWith f A-mu = P+actualMaximumPredecessor (Ordinal.omega0^a)
      (f t-relativeProfile mu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P) := by
    unfold descentWith
    rw [hpart,hnorm]
    simpa only [add_zero,relativeMaximum] using hm
  have hn' : descentWith f A'-nu = P+actualMaximumPredecessor (Ordinal.omega0^a)
      (f t-relativeProfile nu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P) := by
    unfold descentWith
    rw [hpart',hnorm']
    simpa only [add_zero,relativeMaximum] using hn
  have hAl : Order.IsSuccLimit (mu+(P+Ordinal.omega0^a+0)) :=
    Ordinal.isSuccLimit_add mu (unit_gap_limit P a 0 hap (Or.inl rfl))
  have hAl' : Order.IsSuccLimit (nu+(P+Ordinal.omega0^a+0)) :=
    Ordinal.isSuccLimit_add nu (unit_gap_limit P a 0 hap (Or.inl rfl))
  have hAn : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit hAl).trans
    (by rw [← hpart]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have hAn' : Ordinal.omega0 ≤ A' := (Ordinal.omega0_le_of_isSuccLimit hAl').trans
    (by rw [← hpart']; exact Ordinal.mul_div_le A' Ordinal.omega0)
  refine ⟨hm',hn',?_,?_,?_,?_⟩
  · rw [descent_norm f A hAn hA,hnorm]
  · rw [descent_norm f A' hAn' hA',hnorm']
  · rw [hm']
    have h := actualLimitPartMonotone (show P ≤ P+actualMaximumPredecessor (Ordinal.omega0^a) (f t-relativeProfile mu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P) from le_self_add)
    rwa [hPt] at h
  · rw [hn']
    have h := actualLimitPartMonotone (show P ≤ P+actualMaximumPredecessor (Ordinal.omega0^a) (f t-relativeProfile nu (Ordinal.log Ordinal.omega0 P)-actualOrdinalNorm P) from le_self_add)
    rwa [hPt] at h

end LogicLineages.PermittedControl
