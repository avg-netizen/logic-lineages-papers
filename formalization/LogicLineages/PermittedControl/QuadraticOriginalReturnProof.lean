module
public import LogicLineages.PermittedControl.QuadraticExceptionReturnProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem sensitive_tail_double (R B t : Nat) (ht : thickBlockTail R B ≤ t) : 2*R+10 ≤ t := by
  have hb : 100*(R+2)^4 ≤ t := (le_max_left _ _).trans ht
  have hp : R+2 ≤ (R+2)^4 := Nat.le_self_pow (by omega : 4 ≠ 0) (R+2)
  omega

/-- Original quadratic unit with an arbitrary original finite omega-tail;
initial and generated-tail clocks are both paid. -/
 theorem quadratic_original_return (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P A A' : Ordinal.{0}) (n R t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hP : P < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hPpos : 0 < P) (hd : Ordinal.omega0^(2 : Ordinal) ∣ P)
    (hR : 20 ≤ R) (hmuR : actualOrdinalNorm mu ≤ R) (hnuR : actualOrdinalNorm nu ≤ R)
    (hPR : actualOrdinalNorm P ≤ R) (ht : thickBlockTail R B ≤ t)
    (hp : actualLimitPart A=mu+((P+Ordinal.omega0^(2 : Ordinal))+Ordinal.omega0*(n : Ordinal)))
    (hp' : actualLimitPart A'=nu+((P+Ordinal.omega0^(2 : Ordinal))+Ordinal.omega0*(n : Ordinal)))
    (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hex : relativeProfile nu (Ordinal.log Ordinal.omega0 P)=relativeProfile mu (Ordinal.log Ordinal.omega0 P)+1 ∧
      (relativeProfile mu (Ordinal.log Ordinal.omega0 P)+actualOrdinalNorm P)%2=1) :
    ∃ j : Nat, FirstEntry f A (mu+P) j ∧ FirstEntry f A' (nu+P) j ∧
      actualOrdinalNorm ((descentWith f)^[j] A)=f^[j] t ∧
      actualOrdinalNorm ((descentWith f)^[j] A')=f^[j] t := by
  let H := P+Ordinal.omega0^(2 : Ordinal)
  have ha : (2 : Ordinal.{0}) < epsilonZero := by simpa using finiteCoefficient_below 0 2
  have hH : H < epsilonZero := epsilonZero_add_principal hP (phase_power_below 2 ha)
  have hHl : Order.IsSuccLimit H := Ordinal.isSuccLimit_add P
    (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (by norm_num))
  have hPl := retained_prefix_limit P 2 hPpos (by norm_num) hd
  have hN2 : actualOrdinalNorm (2 : Ordinal)=2 := by simpa using actualFiniteHeadNorm 0 2
  have hHN : actualOrdinalNorm H=actualOrdinalNorm P+3 := by
    have h := thick_block_norm P 2 1 hP ha hd
    simpa only [thickBlock,Nat.cast_one,mul_one,hN2] using h
  have hheadl : Order.IsSuccLimit (H+Ordinal.omega0*(n : Ordinal)) := by
    by_cases hn0 : n=0
    · simpa [hn0] using hHl
    · exact Ordinal.isSuccLimit_add H (Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
        (by exact_mod_cast Nat.pos_of_ne_zero hn0))
  have hhead := actual_limit_norm_le A _ hA (Ordinal.isSuccLimit_add mu hheadl) hp
  have hhead' := actual_limit_norm_le A' _ hA' (Ordinal.isSuccLimit_add nu hheadl) hp'
  rw [hn] at hhead
  rw [hn'] at hhead'
  have hmN := relativeNorm mu H hmu hH
  have hnN := relativeNorm nu H hnu hH
  have hlarge := sensitive_tail_double R B t ht
  have hg : max 2 (max (actualOrdinalNorm (mu+(H+Ordinal.omega0*(n : Ordinal))))
      (max (actualOrdinalNorm (nu+(H+Ordinal.omega0*(n : Ordinal))))
        (max (actualOrdinalNorm (mu+H)+3) (actualOrdinalNorm (nu+H)+3)))) ≤ t := by omega
  have hi := actualLinearReturn f B hf mu nu H A A' n t hmu hnu hH hA hA' hHl hp hp' hn hn' hg
  have hAi := trajectory_below f A hA n
  have hAi' := trajectory_below f A' hA' n
  have hparts := (interval_iff_limitPart _ (mu+H) (Or.inr (Ordinal.isSuccLimit_add mu hHl))).mp ⟨hi.1.1,hi.1.2.1⟩
  have hparts' := (interval_iff_limitPart _ (nu+H) (Or.inr (Ordinal.isSuccLimit_add nu hHl))).mp ⟨hi.2.1.1,hi.2.1.2.1⟩
  have hts : thickBlockTail R B ≤ f^[n] t := ht.trans (iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) n t)
  have hsetup : Targets.SensitiveUnitSetup f B mu nu P 2 0 ((descentWith f)^[n] A) ((descentWith f)^[n] A') R (f^[n] t) := by
    refine ⟨hf,hmu,hnu,hP,ha,hAi,hAi',hmud,hnud,hPpos,le_rfl,hd,?_,Or.inl rfl,hR,hmuR,hnuR,hPR,?_,hts,?_,?_,hi.2.2.1,hi.2.2.2.1,?_⟩
    · exact Ordinal.opow_pos _ Ordinal.omega0_pos
    · rw [hN2]; omega
    · simpa only [add_zero] using hparts
    · simpa only [add_zero] using hparts'
    · omega
  obtain ⟨j,hj,hj',hNj,hNj'⟩ := quadratic_exception_return f B mu nu P _ _ R _ hsetup hex
  have hw : Ordinal.omega0 ≤ Ordinal.omega0^(2 : Ordinal) := Ordinal.left_le_opow _ (by norm_num)
  have hgap : (mu+P)+Ordinal.omega0 ≤ mu+H := by simpa only [H,add_assoc] using (add_le_add_iff_left (mu+P)).mpr hw
  have hgap' : (nu+P)+Ordinal.omega0 ≤ nu+H := by simpa only [H,add_assoc] using (add_le_add_iff_left (nu+P)).mpr hw
  refine ⟨n+j,firstEntry_compose f A (mu+H) (mu+P) n j hA hgap hi.1 hj,
    firstEntry_compose f A' (nu+H) (nu+P) n j hA' hgap' hi.2.1 hj',?_,?_⟩
  · simpa only [Nat.add_comm n j,Function.iterate_add_apply] using hNj
  · simpa only [Nat.add_comm n j,Function.iterate_add_apply] using hNj'

end LogicLineages.PermittedControl
