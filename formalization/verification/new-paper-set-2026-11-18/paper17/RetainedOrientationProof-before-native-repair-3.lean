module
public import LogicLineages.PermittedControl.SensitiveQuadraticProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem relative_trajectory_antitone (f : Nat → Nat) (A mu : Ordinal.{0}) (hA : A < epsilonZero) :
    Antitone (fun i : Nat => (descentWith f)^[i] A-mu) := by
  intro i j hij
  apply Ordinal.sub_le.mpr
  exact (trajectory_antitone f A hA hij).trans (Ordinal.le_add_sub _ _)

 theorem relative_limit_trajectory_antitone (f : Nat → Nat) (A mu : Ordinal.{0}) (hA : A < epsilonZero) :
    Antitone (fun i : Nat => actualLimitPart ((descentWith f)^[i] A-mu)) := by
  intro i j hij
  exact actualLimitPartMonotone (relative_trajectory_antitone f A mu hA hij)

 theorem trajectory_norm_nonfinite (f : Nat → Nat) (A : Ordinal.{0}) (hA : A < epsilonZero)
    (i : Nat) (hi : Ordinal.omega0 ≤ (descentWith f)^[i] A) :
    actualOrdinalNorm ((descentWith f)^[i] A)=f^[i] (actualOrdinalNorm A) := by
  apply trajectory_norm f A hA i
  by_contra h
  exact (not_lt_of_ge hi) (actual_after_terminal_finite f A hA i (by omega))

 theorem retained_band_cost (mu P y : Ordinal.{0}) (hP : 0 < P) (hPy : P ≤ y)
    (hy : y < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1)) :
    relativeCost mu y=relativeProfile mu (Ordinal.log Ordinal.omega0 P) := by
  have hypos : 0 < y := hP.trans_le hPy
  have hlog : Ordinal.log Ordinal.omega0 y=Ordinal.log Ordinal.omega0 P := by
    apply le_antisymm
    · exact Order.lt_add_one_iff.mp ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hypos.ne').mp hy)
    · exact Ordinal.log_mono_right _ hPy
  simp only [relativeCost,hypos.ne',↓reduceIte,hlog]

/-- Orientation at the first actual divergence while both states remain in a
common retained-leading band. No sign conclusion is imported from thick. -/
 theorem first_retained_divergence_oriented (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P A A' : Ordinal.{0}) (t i : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hP : Ordinal.omega0 ≤ P) (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hmut : actualOrdinalNorm mu ≤ t) (hnut : actualOrdinalNorm nu ≤ t)
    (hband : A-mu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1))
    (hband' : A'-nu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1))
    (hstart : actualLimitPart (A-mu)=actualLimitPart (A'-nu))
    (hcost : relativeProfile mu (Ordinal.log Ordinal.omega0 P) ≤ relativeProfile nu (Ordinal.log Ordinal.omega0 P))
    (hfirst : ∀ j < i, actualLimitPart ((descentWith f)^[j] A-mu)=actualLimitPart ((descentWith f)^[j] A'-nu))
    (hne : actualLimitPart ((descentWith f)^[i] A-mu) ≠ actualLimitPart ((descentWith f)^[i] A'-nu))
    (hkeep : P ≤ actualLimitPart ((descentWith f)^[i] A-mu))
    (hkeep' : P ≤ actualLimitPart ((descentWith f)^[i] A'-nu)) :
    actualLimitPart ((descentWith f)^[i] A'-nu) < actualLimitPart ((descentWith f)^[i] A-mu) := by
  have hipos : 0 < i := by
    by_contra h
    have : i=0 := by omega
    subst i
    exact hne hstart
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hipos.ne'
  let U := (descentWith f)^[k] A-mu
  let V := (descentWith f)^[k] A'-nu
  let u := f^[k+1] t
  have hPk : P ≤ actualLimitPart U := hkeep.trans (relative_limit_trajectory_antitone f A mu hA (by omega))
  have hPk' : P ≤ actualLimitPart V := hkeep'.trans (relative_limit_trajectory_antitone f A' nu hA' (by omega))
  have hUw : Ordinal.omega0 ≤ U := hP.trans (hPk.trans (Ordinal.mul_div_le U Ordinal.omega0))
  have hVw : Ordinal.omega0 ≤ V := hP.trans (hPk'.trans (Ordinal.mul_div_le V Ordinal.omega0))
  have hwhole : (descentWith f)^[k] A = mu+U := by
    apply (Ordinal.add_sub_cancel_of_le ?_).symm
    simpa only [add_zero] using (Ordinal.lt_sub.mp (Ordinal.omega0_pos.trans_le hUw)).le
  have hwhole' : (descentWith f)^[k] A' = nu+V := by
    apply (Ordinal.add_sub_cancel_of_le ?_).symm
    simpa only [add_zero] using (Ordinal.lt_sub.mp (Ordinal.omega0_pos.trans_le hVw)).le
  have hUk := trajectory_below f A hA k
  have hVk := trajectory_below f A' hA' k
  have hNU := trajectory_norm_nonfinite f A hA k (hUw.trans (Ordinal.sub_le_self _ _))
  have hNV := trajectory_norm_nonfinite f A' hA' k (hVw.trans (Ordinal.sub_le_self _ _))
  rw [hn] at hNU
  rw [hn'] at hNV
  have htu : t ≤ u := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) (k+1) t
  have hbud : f (actualOrdinalNorm (mu+U))=u := by dsimp only [u]; rw [← hwhole,hNU,Function.iterate_succ_apply']
  have hbud' : f (actualOrdinalNorm (nu+V))=u := by dsimp only [u]; rw [← hwhole',hNV,Function.iterate_succ_apply']
  have hstep := (relativeDescentStep f mu U (by rwa [← hwhole]) hmud hUw (by rw [hbud]; exact hmut.trans htu)).2
  have hstep' := (relativeDescentStep f nu V (by rwa [← hwhole']) hnud hVw (by rw [hbud']; exact hnut.trans htu)).2
  rw [hbud] at hstep
  rw [hbud'] at hstep'
  have hnext : (descentWith f)^[k+1] A-mu = relativeMaximum mu (actualLimitPart U) u := by
    rw [Function.iterate_succ_apply',hwhole,hstep,Ordinal.add_sub_cancel]
  have hnext' : (descentWith f)^[k+1] A'-nu = relativeMaximum nu (actualLimitPart V) u := by
    rw [Function.iterate_succ_apply',hwhole',hstep',Ordinal.add_sub_cancel]
  have hlim : actualLimitPart U=actualLimitPart V := hfirst k (by omega)
  have hpos : 0 < actualLimitPart U := Ordinal.omega0_pos.trans_le (hP.trans hPk)
  have hab : mu+actualLimitPart U < epsilonZero :=
    ((add_le_add_iff_left mu).mpr (Ordinal.mul_div_le U Ordinal.omega0)).trans_lt (by rwa [← hwhole])
  have hab' : nu+actualLimitPart V < epsilonZero :=
    ((add_le_add_iff_left nu).mpr (Ordinal.mul_div_le V Ordinal.omega0)).trans_lt (by rwa [← hwhole'])
  have hmax := (relativeMaximumSpec mu _ u hab hpos (hmut.trans htu)).2
  have hmax' := (relativeMaximumSpec nu _ u hab' (by rwa [← hlim]) (hnut.trans htu)).2
  let w := (descentWith f)^[k+1] A'-nu
  have hPw : P ≤ w := hkeep'.trans (Ordinal.mul_div_le w Ordinal.omega0)
  have hwb : w < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    (relative_trajectory_antitone f A' nu hA' (Nat.zero_le _)).trans_lt hband'
  have hcm := retained_band_cost mu P w (Ordinal.omega0_pos.trans_le hP) hPw hwb
  have hcn := retained_band_cost nu P w (Ordinal.omega0_pos.trans_le hP) hPw hwb
  have hwmem : w < actualLimitPart U ∧ actualOrdinalNorm w+relativeCost nu w ≤ u := by
    dsimp [w]
    rw [hnext',hlim]
    exact hmax'.1
  have hwle : w ≤ relativeMaximum mu (actualLimitPart U) u := by
    apply hmax.2
    refine ⟨hwmem.1,?_⟩
    have h := hwmem.2
    rw [hcn] at h
    rw [hcm]
    omega
  have hle := actualLimitPartMonotone hwle
  rw [← hnext] at hle
  exact lt_of_le_of_ne hle (Ne.symm hne)

 theorem retained_divergence_oriented (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P A A' : Ordinal.{0}) (t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hP : Ordinal.omega0 ≤ P) (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hmut : actualOrdinalNorm mu ≤ t) (hnut : actualOrdinalNorm nu ≤ t)
    (hband : A-mu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1))
    (hband' : A'-nu < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1))
    (hstart : actualLimitPart (A-mu)=actualLimitPart (A'-nu))
    (hcost : relativeProfile mu (Ordinal.log Ordinal.omega0 P) ≤ relativeProfile nu (Ordinal.log Ordinal.omega0 P))
    (hex : ∃ i : Nat,
      actualLimitPart ((descentWith f)^[i] A-mu) ≠ actualLimitPart ((descentWith f)^[i] A'-nu) ∧
      P ≤ actualLimitPart ((descentWith f)^[i] A-mu) ∧ P ≤ actualLimitPart ((descentWith f)^[i] A'-nu)) :
    Targets.OrientedUnitDivergence f mu nu P A A' := by
  classical
  obtain ⟨h,hh,hkeep,hkeep'⟩ := hex
  have he : ∃ i : Nat, actualLimitPart ((descentWith f)^[i] A-mu) ≠
      actualLimitPart ((descentWith f)^[i] A'-nu) := ⟨h,hh⟩
  let i := Nat.find he
  have hih : i ≤ h := Nat.find_min' he hh
  have hi := Nat.find_spec he
  have hfirst : ∀ j < i, actualLimitPart ((descentWith f)^[j] A-mu)=actualLimitPart ((descentWith f)^[j] A'-nu) := by
    intro j hj
    exact not_not.mp (Nat.find_min he hj)
  have hk := hkeep.trans (relative_limit_trajectory_antitone f A mu hA hih)
  have hk' := hkeep'.trans (relative_limit_trajectory_antitone f A' nu hA' hih)
  exact ⟨i,first_retained_divergence_oriented f B hf mu nu P A A' t i hmu hnu hA hA' hmud hnud
    hP hn hn' hmut hnut hband hband' hstart hcost hfirst hi hk hk',hk',hk⟩

end LogicLineages.PermittedControl
