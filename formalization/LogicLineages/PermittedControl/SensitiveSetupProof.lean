module
public import LogicLineages.PermittedControl.RetainedOrientationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem unit_gap_limit (P a r : Ordinal.{0}) (ha : 0 < a) (hr : r=0 ∨ Order.IsSuccLimit r) :
    Order.IsSuccLimit (P+Ordinal.omega0^a+r) := by
  rcases hr with rfl | hr
  · simpa using Ordinal.isSuccLimit_add P (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 ha.ne')
  · exact Ordinal.isSuccLimit_add _ hr

 theorem retained_prefix_nonfinite (P a : Ordinal.{0}) (hP : 0 < P) (ha : 1 ≤ a)
    (hd : Ordinal.omega0^a ∣ P) : Ordinal.omega0 ≤ P := by
  have h := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone ha
  have hw : Ordinal.omega0 ≤ Ordinal.omega0^a := by simpa using h
  exact hw.trans (Ordinal.le_of_dvd hP.ne' hd)

 theorem unit_state_initial (mu P a r A : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hP : P < epsilonZero) (ha : a < epsilonZero)
    (hPpos : 0 < P) (hapos : 0 < a) (hd : Ordinal.omega0^a ∣ P)
    (hr : r < Ordinal.omega0^a) (hrd : r=0 ∨ Order.IsSuccLimit r)
    (hA : A < epsilonZero) (hpart : actualLimitPart A=mu+(P+Ordinal.omega0^a+r))
    (hnorm : actualOrdinalNorm A=t) :
    A=countInitial (mu+(P+Ordinal.omega0^a+r)) t ∧
    actualOrdinalNorm (mu+(P+Ordinal.omega0^a+r)) ≤ t ∧
    actualOrdinalNorm (mu+(P+Ordinal.omega0^a)) ≤ t ∧
    actualLimitPart (A-mu)=P+Ordinal.omega0^a+r ∧
    A-mu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) := by
  let sigma := P+Ordinal.omega0^a+r
  have hpw := phase_power_below a ha
  have hs : sigma < epsilonZero := epsilonZero_add_principal (epsilonZero_add_principal hP hpw) (hr.trans hpw)
  have hsl : Order.IsSuccLimit sigma := unit_gap_limit P a r hapos hrd
  have hhead := epsilonZero_add_principal hmu hs
  have hheadl := Ordinal.isSuccLimit_add mu hsl
  have hn : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit hheadl).trans
    (by rw [← hpart]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have hdec := actualNonfiniteDecomposition A hn hA
  have hAnorm : A=countInitial (mu+sigma) t := actual_phase_normalize (fun n => n) A _ t hhead (Or.inr hheadl) hpart hnorm
  have hheadN : actualOrdinalNorm (mu+sigma) ≤ t := by
    have h := hdec.2.2.2
    rw [hpart,hnorm] at h
    change t=actualOrdinalNorm (mu+sigma)+actualTailPart A at h
    omega
  have htargetN : actualOrdinalNorm (mu+(P+Ordinal.omega0^a)) ≤ t := by
    have h := thick_head_suffix_norm mu P a r 1 hmu hP ha (by omega) hd hr
    simp only [thickBlock,Nat.cast_one,mul_one] at h
    change actualOrdinalNorm (mu+sigma)=actualOrdinalNorm (mu+(P+Ordinal.omega0^a))+actualOrdinalNorm r at h
    omega
  have hstate : A-mu=sigma+(actualTailPart A : Ordinal) := by
    conv_lhs => rw [hdec.2.2.1,hpart,add_assoc,Ordinal.add_sub_cancel]
  have hrelative := limitPart_tail sigma hsl (actualTailPart A)
  have hE : a ≤ Ordinal.log Ordinal.omega0 P := Ordinal.le_log_of_opow_le
    Ordinal.one_lt_omega0 (Ordinal.le_of_dvd hPpos.ne' hd)
  have hPb : P < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
  have hab : Ordinal.omega0^a < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (hE.trans_lt (Order.lt_add_one_iff.mpr le_rfl))
  have hsb : sigma < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    Ordinal.isPrincipal_add_omega0_opow _ (Ordinal.isPrincipal_add_omega0_opow _ hPb hab) (hr.trans hab)
  have hnb : (actualTailPart A : Ordinal) < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    (Ordinal.natCast_lt_omega0 _).trans_le (by
      simpa using (Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone
        (show (1 : Ordinal.{0}) ≤ Ordinal.log Ordinal.omega0 P+1 from le_add_self))
  refine ⟨hAnorm,hheadN,htargetN,?_,?_⟩
  · rw [hstate]
    exact hrelative
  · rw [hstate]
    exact Ordinal.isPrincipal_add_omega0_opow _ hsb hnb

 theorem sensitive_orient (f : Nat → Nat) (B : Nat) (mu nu P a r A A' : Ordinal.{0}) (R t : Nat)
    (hs : Targets.SensitiveUnitSetup f B mu nu P a r A A' R t)
    (hex : ∃ i : Nat,
      actualLimitPart ((descentWith f)^[i] A-mu) ≠ actualLimitPart ((descentWith f)^[i] A'-nu) ∧
      P ≤ actualLimitPart ((descentWith f)^[i] A-mu) ∧ P ≤ actualLimitPart ((descentWith f)^[i] A'-nu)) :
    Targets.OrientedUnitDivergence f mu nu P A A' := by
  rcases hs with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hdiv,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hnorm,hnorm',hcd⟩
  have hap : 0 < a := lt_of_lt_of_le (by norm_num) h2
  have h1 : (1 : Ordinal.{0}) ≤ a := le_trans (by norm_num) h2
  have hpw := retained_prefix_nonfinite P a hPpos h1 hdiv
  have hu := unit_state_initial mu P a r A t hmu hP ha hPpos hap hdiv hr hrd hA hpart hnorm
  have hv := unit_state_initial nu P a r A' t hnu hP ha hPpos hap hdiv hr hrd hA' hpart' hnorm'
  have hlarge := sensitive_tail_large R B t ht
  exact retained_divergence_oriented f B hf mu nu P A A' t hmu hnu hA hA' hmud hnud hpw
    hnorm hnorm' (by omega) (by omega) hu.2.2.2.2 hv.2.2.2.2
    (hu.2.2.2.1.trans hv.2.2.2.1.symm) hcd.le hex

 theorem limitPart_add_limit_left (L x : Ordinal.{0}) (hL : Order.IsSuccLimit L) (hx : x < epsilonZero) :
    actualLimitPart (L+x)=L+actualLimitPart x := by
  by_cases hn : Ordinal.omega0 ≤ x
  · exact phase_limit_add L x hx hn
  · obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp (lt_of_not_ge hn)
    rw [limitPart_finite,add_zero]
    exact limitPart_tail L hL n

end LogicLineages.PermittedControl
