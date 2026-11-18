module
public import LogicLineages.PermittedControl.SensitiveHigherLocalProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem higher_sensitive_top (f : Nat → Nat) (B : Nat) (mu nu P a A A' : Ordinal.{0}) (R t : Nat)
    (hs : Targets.SensitiveUnitSetup f B mu nu P a 0 A A' R t) (ha2 : (2 : Ordinal) < a) :
    Targets.OrientedUnitDivergence f mu nu P A A' := by
  have hstep := sensitive_top_step f B mu nu P a A A' R t hs
  have hs0 := hs
  rcases hs with ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,h2,hdiv,hr,hrd,
    hR,hmuR,hnuR,hPR,haR,ht,hpart,hpart',hnorm,hnorm',hcd⟩
  apply sensitive_orient f B mu nu P a 0 A A' R t hs0
  by_cases heq : actualLimitPart (descentWith f A-mu)=actualLimitPart (descentWith f A'-nu)
  · let u := f t
    let c := relativeProfile mu (Ordinal.log Ordinal.omega0 P)
    let d := relativeProfile nu (Ordinal.log Ordinal.omega0 P)
    let X := u-c-actualOrdinalNorm P
    let Y := u-d-actualOrdinalNorm P
    have hcR : c ≤ R := (relativePrefixNorm mu _ hmu).2.2.trans hmuR
    have hdR : d ≤ R := (relativePrefixNorm nu _ hnu).2.2.trans hnuR
    have hlarge := sensitive_tail_large R B t ht
    have hu : 2*t+4 ≤ u := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
    have hX : 2 ≤ X := by dsimp only [X]; omega
    have hY : 2 ≤ Y := by dsimp only [Y]; omega
    have hYX : Y < X := by dsimp only [X,Y,c,d] at *; omega
    have hEq : actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^a) X)=
        actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^a) Y) := by
      simpa only [hstep.1,hstep.2.1] using heq
    rcases Ordinal.zero_or_succ_or_isSuccLimit a with hz | ⟨a0,haeq⟩ | halim
    · subst a
      norm_num at ha2
    · subst a
      simp only [Order.succ_eq_add_one] at *
      have ha0 : a0 < epsilonZero := (show a0 < a0+1 from Order.lt_add_one_iff.mpr le_rfl).trans ha
      have h2a0 : (2 : Ordinal.{0}) ≤ a0 := by
        exact Order.lt_add_one_iff.mp ha2
      have ha0pos : 0 < a0 := lt_of_lt_of_le (by norm_num) h2a0
      have hnorma : actualOrdinalNorm (a0+1)=1+actualOrdinalNorm a0 := by
        simpa [Nat.add_comm] using (actualFiniteTailClosureNorm a0 ha0 1).2
      let v := 1+actualOrdinalNorm a0
      let q := X/v
      let w := actualMaximumPredecessor (Ordinal.omega0^a0) (X%v)
      let r1 := actualLimitPart w
      have hv : 0 < v := by dsimp only [v]; omega
      have hvR : v ≤ R := by simpa only [hnorma] using haR
      have hq : R+2 < q := sensitive_quotient_large R B t u c (actualOrdinalNorm P) v ht hu hcR hPR hv hvR
      have hqpos : 0 < q := by omega
      have hform := successorLocalTail a0 X ha0 (by
        have hqX := (Nat.le_div_iff_mul_le hv).mp (show 1 ≤ X/v by change 1 ≤ q; omega)
        simpa only [one_mul] using hqX)
      change actualMaximumPredecessor (Ordinal.omega0^(a0+1)) X=Ordinal.omega0^a0*(q : Ordinal)+w at hform
      have hpw := phase_power_below a0 ha0
      have hw : w < Ordinal.omega0^a0 := (actualMaximumPredecessor_correct _
        (Ordinal.opow_pos a0 Ordinal.omega0_pos) hpw (X%v)).1.1
      have hr1 : r1 < Ordinal.omega0^a0 := (Ordinal.mul_div_le w Ordinal.omega0).trans_lt hw
      have hr1d : r1=0 ∨ Order.IsSuccLimit r1 := limitPart_zero_or_limit w
      have hdiv0 : Ordinal.omega0^a0 ∣ P :=
        (Ordinal.opow_dvd_opow Ordinal.omega0 (le_self_add : a0 ≤ a0+1)).trans hdiv
      have hblocklim := thick_block_limit P a0 q ha0pos hqpos
      have hrel : actualLimitPart (descentWith f A-mu)=thickBlock P a0 q+r1 := by
        rw [hstep.1]
        change actualLimitPart (P+actualMaximumPredecessor (Ordinal.omega0^(a0+1)) X)=_
        rw [hform,← add_assoc]
        exact limitPart_add_limit_left _ w hblocklim (hw.trans hpw)
      have hrel' : actualLimitPart (descentWith f A'-nu)=thickBlock P a0 q+r1 := heq.symm.trans hrel
      have hnextA : descentWith f A < epsilonZero := (descent_le f A hA).trans_lt hA
      have hnextA' : descentWith f A' < epsilonZero := (descent_le f A' hA').trans_lt hA'
      have hPw := retained_prefix_nonfinite P (a0+1) hPpos (by exact le_trans (by norm_num) h2) hdiv
      have hnon : Ordinal.omega0 ≤ descentWith f A-mu :=
        hPw.trans (hstep.2.2.2.2.1.trans (Ordinal.mul_div_le _ Ordinal.omega0))
      have hnon' : Ordinal.omega0 ≤ descentWith f A'-nu :=
        hPw.trans (hstep.2.2.2.2.2.trans (Ordinal.mul_div_le _ Ordinal.omega0))
      have hpartN : actualLimitPart (descentWith f A)=mu+(thickBlock P a0 q+r1) := by
        rw [absolute_limit_of_relative mu _ hnextA hnon,hrel]
      have hpartN' : actualLimitPart (descentWith f A')=nu+(thickBlock P a0 q+r1) := by
        rw [absolute_limit_of_relative nu _ hnextA' hnon',hrel']
      have hshift : relativeProfile mu (Ordinal.log Ordinal.omega0 (thickBlock P a0 q)) <
          relativeProfile nu (Ordinal.log Ordinal.omega0 (thickBlock P a0 q)) := by
        rw [thick_block_leading P a0 q hqpos hdiv0]
        simpa only [hPpos.ne',↓reduceIte] using hcd
      obtain ⟨j,hneq,hlo,hlo'⟩ := actualThickBlockSeparation f B hf mu nu P a0 r1
        (descentWith f A) (descentWith f A') R q u hmu hnu hP ha0 hnextA hnextA' hmud hnud h2a0 hdiv0
        hr1 hr1d hR hmuR hnuR (by dsimp only [v] at hvR; omega) hq (ht.trans (by omega))
        hpartN hpartN' hstep.2.2.1 hstep.2.2.2.1 hshift
      refine ⟨j+1,?_,?_,?_⟩
      · simpa only [Function.iterate_succ_apply] using hneq
      · exact (le_self_add : P ≤ thickBlock P a0 (q-2)).trans (by simpa only [Function.iterate_succ_apply] using hlo)
      · exact (le_self_add : P ≤ thickBlock P a0 (q-2)).trans (by simpa only [Function.iterate_succ_apply] using hlo')
    · exact False.elim ((local_limit_separation P a ha h2 halim X Y hX hY hYX) hEq)
  · refine ⟨1,?_,?_,?_⟩
    · simpa only [Function.iterate_one] using heq
    · simpa only [Function.iterate_one] using hstep.2.2.2.2.1
    · simpa only [Function.iterate_one] using hstep.2.2.2.2.2

 theorem higherSensitiveUnit : Targets.HigherSensitiveUnit := by
  intro f B mu nu P a r A A' R t hs ha2
  rcases sensitive_admission f B mu nu P a r A A' R t hs with hd | ⟨i,hi,hj,hstop⟩
  · exact hd
  · obtain ⟨j,hjdiv,hlo,hlo'⟩ := higher_sensitive_top f B mu nu P a ((descentWith f)^[i] A)
      ((descentWith f)^[i] A') R (f^[i] t) hstop ha2
    refine ⟨i+j,?_,?_,?_⟩
    · rw [Nat.add_comm i j,Function.iterate_add_apply]
      exact hjdiv
    · rw [Nat.add_comm i j,Function.iterate_add_apply]
      exact hlo
    · rw [Nat.add_comm i j,Function.iterate_add_apply]
      exact hlo'

 theorem sensitiveUnitFoundation : Targets.SensitiveUnitFoundation :=
  ⟨higherSensitiveUnit,quadraticUnitTop,quadraticUnitAdmission⟩

end LogicLineages.PermittedControl
