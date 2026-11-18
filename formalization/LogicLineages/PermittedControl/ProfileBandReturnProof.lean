module
public import LogicLineages.PermittedControl.ProfileIntervalCouplingProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualProfileBandReturn : Targets.ActualProfileBandReturn := by
  intro f B hf mu nu E zeta A A' R t hmu hnu hE hz hA hA' hmud hnud hz1 hzE hR hmuR hnuR hER hzR ht hpart hpart' hN hN' hprofiles
  let P := Ordinal.omega0^zeta
  let Y := Ordinal.omega0^E
  have hzpos : 0 < zeta := (by norm_num : (0 : Ordinal) < 1).trans_le hz1
  have hEpos : 0 < E := hzpos.trans_le hzE
  have hP := phase_power_below zeta hz
  have hY := phase_power_below E hE
  have hPpos : 0 < P := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hYpos : 0 < Y := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hPl : Order.IsSuccLimit P := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hzpos.ne'
  have hYl : Order.IsSuccLimit Y := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hEpos.ne'
  have htargetl := Ordinal.isSuccLimit_add mu hPl
  have htargetl' := Ordinal.isSuccLimit_add nu hPl
  have hstartl := Ordinal.isSuccLimit_add mu hYl
  have hstartl' := Ordinal.isSuccLimit_add nu hYl
  have hstart := (interval_iff_limitPart A _ (Or.inr hstartl)).mpr hpart
  have hstart' := (interval_iff_limitPart A' _ (Or.inr hstartl')).mpr hpart'
  have hex : ∃ i : Nat, FirstEntry f A (mu+P) i ∧ FirstEntry f A' (nu+P) i := by
    by_cases heq : zeta=E
    · have hPY : P=Y := congrArg (fun e : Ordinal => Ordinal.omega0^e) heq
      refine ⟨0,?_,?_⟩
      · exact ⟨by simpa only [Function.iterate_zero_apply,hPY] using hstart.1,
          by simpa only [Function.iterate_zero_apply,hPY] using hstart.2,by intro j hj; omega⟩
      · exact ⟨by simpa only [Function.iterate_zero_apply,hPY] using hstart'.1,
          by simpa only [Function.iterate_zero_apply,hPY] using hstart'.2,by intro j hj; omega⟩
    · have hzlt : zeta < E := lt_of_le_of_ne hzE heq
      have hPY : P < Y := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono hzlt
      have hcost : ∀ z : Ordinal.{0}, P ≤ z → z < Y → relativeCost mu z=relativeCost nu z := by
        intro z hPz hzY
        have hzpos' : 0 < z := hPpos.trans_le hPz
        have hloglo : zeta ≤ Ordinal.log Ordinal.omega0 z := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hPz
        have hloghi : Ordinal.log Ordinal.omega0 z < E := (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hzpos'.ne').mp hzY
        simpa only [relativeCost,if_neg hzpos'.ne'] using hprofiles _ hloglo hloghi
      have hPN : actualOrdinalNorm P=1+actualOrdinalNorm zeta := by
        simpa only [Nat.cast_one,mul_one,one_mul] using thick_monomial_norm zeta hz 1
      have hlarge := sensitive_tail_double R B t ht
      have hprefix : max (actualOrdinalNorm mu) (actualOrdinalNorm nu) ≤ t := by omega
      have hmP := relativeNorm mu P hmu hP
      have hnP := relativeNorm nu P hnu hP
      have htarget : actualOrdinalNorm (mu+P) ≤ t := by omega
      have htarget' : actualOrdinalNorm (nu+P) ≤ t := by omega
      let u := f t
      have htu : t ≤ u := control_self_le f (selected_threshold_admissible f B hf).2 t
      have hmuU : actualOrdinalNorm mu ≤ u := hmuR.trans (by omega)
      have hnuU : actualOrdinalNorm nu ≤ u := hnuR.trans (by omega)
      have hm := relativeMaximumSpec mu Y u (epsilonZero_add_principal hmu hY) hYpos hmuU
      have hn := relativeMaximumSpec nu Y u (epsilonZero_add_principal hnu hY) hYpos hnuU
      have hPm : P ≤ relativeMaximum mu Y u := hm.2.2 ⟨hPY,by rw [← hmP.1]; exact htarget.trans htu⟩
      have hPn : P ≤ relativeMaximum nu Y u := hn.2.2 ⟨hPY,by rw [← hnP.1]; exact htarget'.trans htu⟩
      have heqm : relativeMaximum mu Y u=relativeMaximum nu Y u := by
        apply le_antisymm
        · apply hn.2.2
          refine ⟨hm.2.1.1,?_⟩
          have hh := hm.2.1.2
          rwa [hcost _ hPm hm.2.1.1] at hh
        · apply hm.2.2
          refine ⟨hn.2.1.1,?_⟩
          have hh := hn.2.1.2
          rwa [← hcost _ hPn hn.2.1.1] at hh
      have hstep : descentWith f A=mu+relativeMaximum mu Y u := by
        unfold descentWith
        rw [hpart,hN]
        exact hm.1
      have hstep' : descentWith f A'=nu+relativeMaximum mu Y u := by
        unfold descentWith
        rw [hpart',hN']
        exact hn.1.trans (congrArg (fun z : Ordinal => nu+z) heqm.symm)
      have hnon : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit hstartl).trans hstart.1
      have hnextN : actualOrdinalNorm (mu+relativeMaximum mu Y u)=u := by
        rw [← hstep,descent_norm f A hnon hA,hN]
      obtain ⟨i,hi,hi'⟩ := equal_profile_interval_return f B hf mu nu P Y hmu hnu hP hPl hmud hnud hcost
        _ (hm.2.1.1.trans hY) hPm hm.2.1.1 (by rw [hnextN]; exact htarget.trans htu)
        (by rw [hnextN]; exact hprefix.trans htu)
      have hw : Ordinal.omega0 < Y := by
        have hh := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (hz1.trans_lt hzlt)
        simpa only [Ordinal.opow_one] using hh
      have hPYskip : P+Ordinal.omega0 ≤ Y := (Ordinal.isPrincipal_add_omega0_opow E hPY hw).le
      have hskip : (mu+P)+Ordinal.omega0 ≤ A := by
        have hh := (add_le_add_iff_left mu).mpr hPYskip
        exact (by simpa only [add_assoc] using hh : (mu+P)+Ordinal.omega0 ≤ mu+Y).trans hstart.1
      have hskip' : (nu+P)+Ordinal.omega0 ≤ A' := by
        have hh := (add_le_add_iff_left nu).mpr hPYskip
        exact (by simpa only [add_assoc] using hh : (nu+P)+Ordinal.omega0 ≤ nu+Y).trans hstart'.1
      refine ⟨1+i,firstEntry_prepend f A (mu+P) i hskip ?_,firstEntry_prepend f A' (nu+P) i hskip' ?_⟩
      · rwa [hstep]
      · rwa [hstep']
  obtain ⟨i,hi,hi'⟩ := hex
  refine ⟨i,hi,hi',?_,?_⟩
  · rw [← hN]
    exact trajectory_norm_nonfinite f A hA i ((Ordinal.omega0_le_of_isSuccLimit htargetl).trans hi.1)
  · rw [← hN']
    exact trajectory_norm_nonfinite f A' hA' i ((Ordinal.omega0_le_of_isSuccLimit htargetl').trans hi'.1)

end LogicLineages.PermittedControl
