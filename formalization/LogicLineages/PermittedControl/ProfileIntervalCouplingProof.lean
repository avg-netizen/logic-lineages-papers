module
public import LogicLineages.PermittedControl.ProfileBandReturnTargets
public import LogicLineages.PermittedControl.InitialPeelingProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Pointwise actual relative-cost equality gives genuine equal first-hit clocks. The
proof couples actual maxima, not only their current limit parts. -/
 theorem equal_profile_interval_return (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P Y : Ordinal.{0}) (hmu : mu < epsilonZero) (hnu : nu < epsilonZero)
    (hP : P < epsilonZero) (hPl : Order.IsSuccLimit P)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hcost : ∀ z : Ordinal.{0}, P ≤ z → z < Y → relativeCost mu z=relativeCost nu z) :
    ∀ y : Ordinal.{0}, y < epsilonZero → P ≤ y →
      y < Y →
      actualOrdinalNorm (mu+P) ≤ actualOrdinalNorm (mu+y) →
      max (actualOrdinalNorm mu) (actualOrdinalNorm nu) ≤ actualOrdinalNorm (mu+y) →
      ∃ i : Nat, FirstEntry f (mu+y) (mu+P) i ∧ FirstEntry f (nu+y) (nu+P) i := by
  intro y
  induction y using Ordinal.lt_wf.induction with
  | h y ih =>
    intro hy hPy hband hbudget hprefixbudget
    have hA := epsilonZero_add_principal hmu hy
    have hA' := epsilonZero_add_principal hnu hy
    have htarget := epsilonZero_add_principal hmu hP
    have htarget' := epsilonZero_add_principal hnu hP
    have hPlow : Ordinal.omega0 ≤ P := Ordinal.omega0_le_of_isSuccLimit hPl
    have hnon : Ordinal.omega0 ≤ y := hPlow.trans hPy
    have hcy := hcost y hPy hband
    have hN : actualOrdinalNorm (mu+y)=actualOrdinalNorm (nu+y) := by
      rw [(relativeNorm mu y hmu hy).1,(relativeNorm nu y hnu hy).1,hcy]
    have hPband : P < Y := hPy.trans_lt hband
    have hcP := hcost P le_rfl hPband
    have hNP : actualOrdinalNorm (mu+P)=actualOrdinalNorm (nu+P) := by
      rw [(relativeNorm mu P hmu hP).1,(relativeNorm nu P hnu hP).1,hcP]
    by_cases hhit : y < P+Ordinal.omega0
    · refine ⟨0,?_,?_⟩
      · exact ⟨(add_le_add_iff_left mu).mpr hPy,by simpa only [Function.iterate_zero_apply,add_assoc] using (add_lt_add_iff_left mu).mpr hhit,by intro j hj; omega⟩
      · exact ⟨(add_le_add_iff_left nu).mpr hPy,by simpa only [Function.iterate_zero_apply,add_assoc] using (add_lt_add_iff_left nu).mpr hhit,by intro j hj; omega⟩
    · have hPfixed : actualLimitPart P=P := by simpa using limitPart_tail P hPl 0
      have hPpart : P ≤ actualLimitPart y := by
        have h := actualLimitPartMonotone hPy
        rwa [hPfixed] at h
      have hPstrict : P < actualLimitPart y := by
        apply lt_of_le_of_ne hPpart
        intro heq
        exact hhit ((interval_iff_limitPart y P (Or.inr hPl)).mpr heq.symm).2
      let u := f (actualOrdinalNorm (mu+y))
      have hbu : actualOrdinalNorm (mu+P) ≤ u :=
        hbudget.trans (control_self_le f (selected_threshold_admissible f B hf).2 _)
      have hbv : actualOrdinalNorm (nu+P) ≤ u := by rwa [← hNP]
      have hprefixU : max (actualOrdinalNorm mu) (actualOrdinalNorm nu) ≤ u :=
        hprefixbudget.trans (control_self_le f (selected_threshold_admissible f B hf).2 _)
      have hmuU : actualOrdinalNorm mu ≤ u := (le_max_left _ _).trans hprefixU
      have hnuU : actualOrdinalNorm nu ≤ u := (le_max_right _ _).trans hprefixU
      have hlim := (actualNonfiniteDecomposition y hnon hy)
      have hab := epsilonZero_add_principal hmu hlim.1
      have hab' := epsilonZero_add_principal hnu hlim.1
      have hm := (relativeMaximumSpec mu (actualLimitPart y) u hab hlim.2.1.bot_lt hmuU).2
      have hn := (relativeMaximumSpec nu (actualLimitPart y) u hab' hlim.2.1.bot_lt hnuU).2
      have hPm : P ≤ relativeMaximum mu (actualLimitPart y) u := hm.2 ⟨hPstrict,by rwa [← (relativeNorm mu P hmu hP).1]⟩
      have hPn : P ≤ relativeMaximum nu (actualLimitPart y) u := hn.2 ⟨hPstrict,by rwa [← (relativeNorm nu P hnu hP).1]⟩
      have hmb := hm.1.1.trans_le (Ordinal.mul_div_le y Ordinal.omega0)
      have hnb := hn.1.1.trans_le (Ordinal.mul_div_le y Ordinal.omega0)
      have hmx := hcost _ hPm (hmb.trans hband)
      have hny := hcost _ hPn (hnb.trans hband)
      have heq : relativeMaximum mu (actualLimitPart y) u=relativeMaximum nu (actualLimitPart y) u := by
        apply le_antisymm
        · apply hn.2
          refine ⟨hm.1.1,?_⟩
          have h := hm.1.2
          rwa [hmx] at h
        · apply hm.2
          refine ⟨hn.1.1,?_⟩
          have h := hn.1.2
          rwa [← hny] at h
      have hstep := (relativeDescentStep f mu y hA hmud hnon hmuU).2
      have hstep' := (relativeDescentStep f nu y hA' hnud hnon (by rw [← hN]; exact hnuU)).2
      change descentWith f (mu+y)=mu+relativeMaximum mu (actualLimitPart y) u at hstep
      rw [← hN,← heq] at hstep'
      have hnextN : actualOrdinalNorm (mu+relativeMaximum mu (actualLimitPart y) u)=u := by
        rw [← hstep,descent_norm f _ (hnon.trans le_add_self) hA]
      obtain ⟨i,hi,hj⟩ := ih _ hmb (hmb.trans hy) hPm (hmb.trans hband) (by rw [hnextN]; exact hbu) (by rw [hnextN]; exact hprefixU)
      have hpre : (mu+P)+Ordinal.omega0 ≤ mu+y := by simpa only [add_assoc] using (add_le_add_iff_left mu).mpr (le_of_not_gt hhit)
      have hpre' : (nu+P)+Ordinal.omega0 ≤ nu+y := by simpa only [add_assoc] using (add_le_add_iff_left nu).mpr (le_of_not_gt hhit)
      refine ⟨1+i,firstEntry_prepend f (mu+y) (mu+P) i hpre ?_,firstEntry_prepend f (nu+y) (nu+P) i hpre' ?_⟩
      · rwa [hstep]
      · rwa [hstep']

end LogicLineages.PermittedControl
