module
public import LogicLineages.PermittedControl.PureSuccessorStepProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem pure_block_unit_le (beta : Ordinal.{0}) (q : Nat) (hq : 0 < q) :
    Ordinal.omega0^beta ≤ Ordinal.omega0^beta*(q : Ordinal) := by
  have h := thick_block_mono 0 beta (show 1 ≤ q by omega)
  simpa only [thickBlock,zero_add,Nat.cast_one,mul_one] using h

 theorem actualPureSuccessorSeparation : Targets.ActualPureSuccessorSeparation := by
  intro f B hf mu nu beta A A' R t hmu hnu hb hA hA' hmud hnud hb2 hR hmuR hnuR hbR ht hp hp' hn hn' hcd
  let u := f t
  let X := u-relativeProfile mu beta
  let v := 1+actualOrdinalNorm beta
  let q := X/v
  let r := actualMaximumPredecessor (Ordinal.omega0^beta) (X%v)
  have hs := actualPureSuccessorStep f B hf mu beta A R t hmu hb hA hmud hb2 hR hmuR hbR ht hp hn
  have hs' := actualPureSuccessorStep f B hf nu beta A' R t hnu hb hA' hnud hb2 hR hnuR hbR ht hp' hn'
  change descentWith f A-mu=Ordinal.omega0^beta*(q : Ordinal)+r ∧ _ at hs
  have hP := phase_power_below beta hb
  have hPpos : 0 < Ordinal.omega0^beta := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hbetapos : 0 < beta := (by norm_num : (0 : Ordinal) < 2).trans_le hb2
  have hPnon : Ordinal.omega0 ≤ Ordinal.omega0^beta := Ordinal.left_le_opow _ hbetapos
  have hnext := (descent_le f A hA).trans_lt hA
  have hnext' := (descent_le f A' hA').trans_lt hA'
  have hlarge := sensitive_tail_double R B t ht
  have htu : t ≤ u := control_self_le f (selected_threshold_admissible f B hf).2 t
  have hmuU : actualOrdinalNorm mu ≤ u := by omega
  have hnuU : actualOrdinalNorm nu ≤ u := by omega
  have hbs : beta+1 < epsilonZero := by simpa using (actualFiniteTailClosureNorm beta hb 1).1
  have hY := phase_power_below (beta+1) hbs
  have hYpos : 0 < Ordinal.omega0^(beta+1) := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hm := relativeMaximumSpec mu (Ordinal.omega0^(beta+1)) u (epsilonZero_add_principal hmu hY) hYpos hmuU
  have hnn := relativeMaximumSpec nu (Ordinal.omega0^(beta+1)) u (epsilonZero_add_principal hnu hY) hYpos hnuU
  have hU : descentWith f A-mu=relativeMaximum mu (Ordinal.omega0^(beta+1)) u := by
    unfold descentWith
    rw [hp,hn]
    rfl
  have hV : descentWith f A'-nu=relativeMaximum nu (Ordinal.omega0^(beta+1)) u := by
    unfold descentWith
    rw [hp',hn']
    rfl
  have hkeep : Ordinal.omega0^beta ≤ actualLimitPart (descentWith f A-mu) := by
    rw [hs.2.2.2.2.2]
    exact (pure_block_unit_le beta q (by have := hs.2.2.1; omega)).trans le_self_add
  have hkeep' : Ordinal.omega0^beta ≤ actualLimitPart (descentWith f A'-nu) := by
    rw [hs'.2.2.2.2.2]
    exact (pure_block_unit_le beta _ (by have := hs'.2.2.1; omega)).trans le_self_add
  have hVpos : 0 < descentWith f A'-nu := hPpos.trans_le
    (hkeep'.trans (Ordinal.mul_div_le _ _))
  have hcostVmu : relativeCost mu (descentWith f A'-nu)=relativeProfile mu beta := by
    simp only [relativeCost,if_neg hVpos.ne',hs'.2.2.2.2.1]
  have hcostVnu : relativeCost nu (descentWith f A'-nu)=relativeProfile nu beta := by
    simp only [relativeCost,if_neg hVpos.ne',hs'.2.2.2.2.1]
  have horder : descentWith f A'-nu ≤ descentWith f A-mu := by
    rw [hU]
    apply hm.2.2
    have hmem := hnn.2.1
    rw [← hV] at hmem
    refine ⟨hmem.1,?_⟩
    rw [hcostVnu] at hmem
    rw [hcostVmu]
    omega
  have hlimorder := actualLimitPartMonotone horder
  by_cases heq : actualLimitPart (descentWith f A-mu)=actualLimitPart (descentWith f A'-nu)
  · have hr := hs.2.2.2.1
    have hrb := hr.trans hP
    have hsigma : actualLimitPart r < Ordinal.omega0^beta := (Ordinal.mul_div_le r Ordinal.omega0).trans_lt hr
    have hsigrd := limitPart_zero_or_limit r
    have habs := absolute_limit_of_relative mu (descentWith f A) hnext
      ((hPnon.trans hkeep).trans (Ordinal.mul_div_le _ _))
    have habs' := absolute_limit_of_relative nu (descentWith f A') hnext'
      ((hPnon.trans hkeep').trans (Ordinal.mul_div_le _ _))
    rw [hs.2.2.2.2.2] at habs
    rw [← heq,hs.2.2.2.2.2] at habs'
    have h0 : (0 : Ordinal.{0}) < epsilonZero := by simpa using finiteCoefficient_below 0 0
    have hlogblock : Ordinal.log Ordinal.omega0 (thickBlock 0 beta q)=beta := by
      simpa using thick_block_leading 0 beta q (by have := hs.2.2.1; omega) (dvd_zero _)
    have hthick := actualThickBlockSeparation f B hf mu nu 0 beta (actualLimitPart r) (descentWith f A) (descentWith f A') R q u
      hmu hnu h0 hb hnext hnext' hmud hnud hb2 (dvd_zero _) hsigma hsigrd hR hmuR hnuR hbR hs.2.2.1
      (ht.trans htu) (by simpa only [thickBlock,zero_add] using habs) (by simpa only [thickBlock,zero_add] using habs')
      hs.2.1 hs'.2.1 (by rwa [hlogblock])
    have hfloor : Ordinal.omega0^beta ≤ thickBlock 0 beta (q-2) := by
      have hh := pure_block_unit_le beta (q-2) (by have := hs.2.2.1; omega)
      simpa only [thickBlock,zero_add] using hh
    have hband : descentWith f A-mu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 (Ordinal.omega0^beta)+1) := by
      rw [Ordinal.log_opow Ordinal.one_lt_omega0]
      rw [hU]
      exact hm.2.1.1
    have hband' : descentWith f A'-nu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 (Ordinal.omega0^beta)+1) := by
      rw [Ordinal.log_opow Ordinal.one_lt_omega0]
      rw [hV]
      exact hnn.2.1.1
    have hdiv := retained_divergence_oriented f B hf mu nu (Ordinal.omega0^beta) (descentWith f A) (descentWith f A') u
      hmu hnu hnext hnext' hmud hnud hPnon hs.2.1 hs'.2.1 hmuU hnuU hband hband' heq
      (by simpa only [Ordinal.log_opow Ordinal.one_lt_omega0] using hcd.le) (by
        obtain ⟨i,hi,hki,hki'⟩ := hthick
        exact ⟨i,hi,hfloor.trans hki,hfloor.trans hki'⟩)
    obtain ⟨i,hi,hki,hki'⟩ := hdiv
    refine ⟨i+1,?_,?_,?_⟩
    · simpa only [Function.iterate_succ_apply] using hi
    · simpa only [Function.iterate_succ_apply] using hki
    · simpa only [Function.iterate_succ_apply] using hki'
  · exact ⟨1,lt_of_le_of_ne hlimorder (Ne.symm heq),hkeep',hkeep⟩

 theorem pureSuccessorFoundation : Targets.PureSuccessorFoundation :=
  ⟨actualPureSuccessorStep,actualPureSuccessorSeparation⟩

end LogicLineages.PermittedControl
