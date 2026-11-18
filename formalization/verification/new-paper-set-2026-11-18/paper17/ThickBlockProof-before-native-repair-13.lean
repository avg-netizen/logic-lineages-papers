module
public import LogicLineages.PermittedControl.ThickTopProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualThickBlockSeparation : Targets.ActualThickBlockSeparation := by
  intro f B hf mu nu P a r A A' R q t hmu hnu hP ha hA hA' hmud hnud h2 hd hr hrd
    hR hmuR hnuR haR hq ht hpart hpart' hnorm hnorm' hshift
  let rho := thickBlock P a q
  let sigma := rho+r
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) h2
  have hqpos : 0 < q := by omega
  have hrho := thick_block_below P a q hP ha
  have hrbelow := hr.trans (phase_power_below a ha)
  have hsigma := epsilonZero_add_principal hrho hrbelow
  have hrhol := thick_block_limit P a q hapos hqpos
  have hsigmal : Order.IsSuccLimit sigma := by
    rcases hrd with hz | hl
    · simpa [sigma,hz] using hrhol
    · exact Ordinal.isSuccLimit_add rho hl
  have hhead := epsilonZero_add_principal hmu hsigma
  have hhead' := epsilonZero_add_principal hnu hsigma
  have hheadl := Ordinal.isSuccLimit_add mu hsigmal
  have hheadl' := Ordinal.isSuccLimit_add nu hsigmal
  have hAnorm : A=countInitial (mu+sigma) t := actual_phase_normalize f A _ t hhead (Or.inr hheadl) hpart hnorm
  have hAnorm' : A'=countInitial (nu+sigma) t := actual_phase_normalize f A' _ t hhead' (Or.inr hheadl') hpart' hnorm'
  have hnon : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit hheadl).trans
    (by rw [← hpart]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have hnon' : Ordinal.omega0 ≤ A' := (Ordinal.omega0_le_of_isSuccLimit hheadl').trans
    (by rw [← hpart']; exact Ordinal.mul_div_le A' Ordinal.omega0)
  have hHN : actualOrdinalNorm (mu+sigma) ≤ t := by
    have h := (actualNonfiniteDecomposition A hnon hA).2.2.2
    rw [hpart,hnorm] at h
    omega
  have hHN' : actualOrdinalNorm (nu+sigma) ≤ t := by
    have h := (actualNonfiniteDecomposition A' hnon' hA').2.2.2
    rw [hpart',hnorm'] at h
    omega
  have hNtarget : actualOrdinalNorm (mu+rho) ≤ t := by
    have h := thick_head_suffix_norm mu P a r q hmu hP ha hqpos hd hr
    change actualOrdinalNorm (mu+sigma)=actualOrdinalNorm (mu+rho)+actualOrdinalNorm r at h
    omega
  have hNtarget' : actualOrdinalNorm (nu+rho) ≤ t := by
    have h := thick_head_suffix_norm nu P a r q hnu hP ha hqpos hd hr
    change actualOrdinalNorm (nu+sigma)=actualOrdinalNorm (nu+rho)+actualOrdinalNorm r at h
    omega
  have ht2 : 2 ≤ t := by
    have hp : 0 < (R+2)^4 := pow_pos (by omega) _
    have hb : 100*(R+2)^4 ≤ t := (le_max_left _ _).trans ht
    omega
  obtain ⟨i,j,hi,hj,hEi,hEj,hguard,hguard',hreset,hdiverge⟩ := synchronizedTargetVisits f B hf
    mu nu sigma rho t hmu hnu hsigma hrho hmud hnud hsigmal hrhol le_self_add (by omega)
  by_cases hij : i=j
  · subst j
    let E := f^[i] t
    have hEt : t ≤ E := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
    have hTE : actualOrdinalNorm (mu+rho) ≤ E :=
      entry_norm_ge_target f _ _ i E (epsilonZero_add_principal hmu hrho) hi hEi
    have hTE' : actualOrdinalNorm (nu+rho) ≤ E :=
      entry_norm_ge_target f _ _ i E (epsilonZero_add_principal hnu hrho) hj hEj
    obtain ⟨k,hsep,hlo,hlo'⟩ := thick_top_separation f B hf mu nu P a R q E hmu hnu hP ha
      hmud hnud h2 hd hR hmuR hnuR haR hq (ht.trans hEt) hTE hTE' hshift
    have hcont : (descentWith f)^[i+k] A = (descentWith f)^[k] (countInitial (mu+rho) E) := by
      rw [hAnorm]
      exact actual_entry_reset_continuation f _ _ i E k (epsilonZero_add_principal hmu hrho) hi hEi
    have hcont' : (descentWith f)^[i+k] A' = (descentWith f)^[k] (countInitial (nu+rho) E) := by
      rw [hAnorm']
      exact actual_entry_reset_continuation f _ _ i E k (epsilonZero_add_principal hnu hrho) hj hEj
    refine ⟨i+k,?_,?_,?_⟩
    · rw [hcont,hcont']
      exact hsep
    · rw [hcont]
      exact hlo
    · rw [hcont']
      exact hlo'
  · obtain ⟨i0,hi0,hne,hlo,hlo'⟩ := hdiverge hij
    have hbase : thickBlock P a (q-2) ≤ rho := thick_block_mono P a (by omega)
    refine ⟨i0,?_,?_,?_⟩
    · rw [hAnorm,hAnorm']
      exact hne
    · rw [hAnorm]
      exact hbase.trans hlo
    · rw [hAnorm']
      exact hbase.trans hlo'

 theorem fullThickBlock : Targets.FullThickBlock := ⟨thickBlockTailEffective,actualThickBlockSeparation⟩

end LogicLineages.PermittedControl
