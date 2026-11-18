module
public import LogicLineages.PermittedControl.QuadraticOriginalReturnProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem double_quadratic_divergence (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu Q A A' : Ordinal.{0}) (n R t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hQ : Q < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hQpos : 0 < Q) (hd : Ordinal.omega0^(2 : Ordinal) ∣ Q)
    (hR : 20 ≤ R) (hmuR : actualOrdinalNorm mu ≤ R) (hnuR : actualOrdinalNorm nu ≤ R)
    (hPR : actualOrdinalNorm (Q+Ordinal.omega0^(2 : Ordinal)) ≤ R)
    (ht : thickBlockTail R B ≤ t)
    (hp : actualLimitPart A=mu+((Q+Ordinal.omega0^(2 : Ordinal))+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal)))
    (hp' : actualLimitPart A'=nu+((Q+Ordinal.omega0^(2 : Ordinal))+Ordinal.omega0^(2 : Ordinal)+Ordinal.omega0*(n : Ordinal)))
    (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hcd : relativeProfile mu (Ordinal.log Ordinal.omega0 Q)<relativeProfile nu (Ordinal.log Ordinal.omega0 Q)) :
    Targets.OrientedUnitDivergence f mu nu Q A A' := by
  let P := Q+Ordinal.omega0^(2 : Ordinal)
  have ha : (2 : Ordinal.{0}) < epsilonZero := by simpa using finiteCoefficient_below 0 2
  have hP : P < epsilonZero := epsilonZero_add_principal hQ (phase_power_below 2 ha)
  have hPpos : 0 < P := hQpos.trans_le le_self_add
  have hPd : Ordinal.omega0^(2 : Ordinal) ∣ P := hd.add dvd_rfl
  have hlog : Ordinal.log Ordinal.omega0 P=Ordinal.log Ordinal.omega0 Q := by
    have h := thick_block_leading Q 2 1 (by omega) hd
    simpa only [thickBlock,Nat.cast_one,mul_one,if_neg hQpos.ne'] using h
  have hN2 : actualOrdinalNorm (2 : Ordinal)=2 := by simpa using actualFiniteHeadNorm 0 2
  have hPN : actualOrdinalNorm P=actualOrdinalNorm Q+3 := by
    have h := thick_block_norm Q 2 1 hQ ha hd
    simpa only [thickBlock,Nat.cast_one,mul_one,hN2] using h
  have hQR : actualOrdinalNorm Q ≤ R := by omega
  have hPl := retained_prefix_limit P 2 hPpos (by norm_num) hPd
  have hQl := retained_prefix_limit Q 2 hQpos (by norm_num) hd
  have hr : Ordinal.omega0*(n : Ordinal) < Ordinal.omega0^(2 : Ordinal) := by
    have h := Ordinal.opow_mul_lt_opow (u := (1 : Ordinal)) (x := (2 : Ordinal)) (Ordinal.natCast_lt_omega0 n) (by norm_num)
    simpa using h
  have hrd : Ordinal.omega0*(n : Ordinal)=0 ∨ Order.IsSuccLimit (Ordinal.omega0*(n : Ordinal)) := by
    by_cases hn0 : n=0
    · left; simp [hn0]
    · right
      exact Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0 (by exact_mod_cast Nat.pos_of_ne_zero hn0)
  have hs : Targets.SensitiveUnitSetup f B mu nu P 2 (Ordinal.omega0*(n : Ordinal)) A A' R t := by
    refine ⟨hf,hmu,hnu,hP,ha,hA,hA',hmud,hnud,hPpos,le_rfl,hPd,hr,hrd,hR,hmuR,hnuR,hPR,?_,ht,hp,hp',hn,hn',?_⟩
    · rw [hN2]; omega
    · rwa [hlog]
  rcases quadraticUnitAdmission f B mu nu P (Ordinal.omega0*(n : Ordinal)) A A' R t hs with hdiv | ⟨hadj,hodd,hrest⟩
  · obtain ⟨i,hi,hkeep,hkeep'⟩ := hdiv
    exact ⟨i,hi,le_self_add.trans hkeep,le_self_add.trans hkeep'⟩
  · obtain ⟨i,hi,hi',hNi,hNi'⟩ := quadratic_original_return f B hf mu nu P A A' n R t hmu hnu hP hA hA' hmud hnud hPpos hPd
      hR hmuR hnuR hPR ht hp hp' hn hn' ⟨hadj,hodd⟩
    have hAi := trajectory_below f A hA i
    have hAi' := trajectory_below f A' hA' i
    have hparts := (interval_iff_limitPart _ (mu+P) (Or.inr (Ordinal.isSuccLimit_add mu hPl))).mp ⟨hi.1,hi.2.1⟩
    have hparts' := (interval_iff_limitPart _ (nu+P) (Or.inr (Ordinal.isSuccLimit_add nu hPl))).mp ⟨hi'.1,hi'.2.1⟩
    have hts : thickBlockTail R B ≤ f^[i] t := ht.trans (iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t)
    have hs' : Targets.SensitiveUnitSetup f B mu nu Q 2 0 ((descentWith f)^[i] A) ((descentWith f)^[i] A') R (f^[i] t) := by
      refine ⟨hf,hmu,hnu,hQ,ha,hAi,hAi',hmud,hnud,hQpos,le_rfl,hd,?_,Or.inl rfl,hR,hmuR,hnuR,hQR,?_,hts,?_,?_,hNi,hNi',hcd⟩
      · exact Ordinal.opow_pos _ Ordinal.omega0_pos
      · rw [hN2]; omega
      · simpa only [add_zero] using hparts
      · simpa only [add_zero] using hparts'
    rcases quadraticUnitAdmission f B mu nu Q 0 _ _ R (f^[i] t) hs' with hdiv | ⟨hadj',hodd',hrest'⟩
    · obtain ⟨j,hj,hkeep,hkeep'⟩ := hdiv
      refine ⟨i+j,?_,?_,?_⟩
      · simpa only [Nat.add_comm i j,Function.iterate_add_apply] using hj
      · simpa only [Nat.add_comm i j,Function.iterate_add_apply] using hkeep
      · simpa only [Nat.add_comm i j,Function.iterate_add_apply] using hkeep'
    · rw [hlog,hPN] at hodd
      omega

end LogicLineages.PermittedControl
