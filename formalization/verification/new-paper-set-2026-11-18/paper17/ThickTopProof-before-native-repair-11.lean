module
public import LogicLineages.PermittedControl.ThickEntryResidueProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem thick_top_separation (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu P a : Ordinal.{0}) (R q t : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hP : P < epsilonZero) (ha : a < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (h2 : (2 : Ordinal) ≤ a) (hd : Ordinal.omega0^a ∣ P)
    (hR : 20 ≤ R) (hmuR : actualOrdinalNorm mu ≤ R) (hnuR : actualOrdinalNorm nu ≤ R)
    (haR : actualOrdinalNorm a ≤ R) (hq : R+2 < q) (ht : thickBlockTail R B ≤ t)
    (hhead : actualOrdinalNorm (mu+thickBlock P a q) ≤ t)
    (hhead' : actualOrdinalNorm (nu+thickBlock P a q) ≤ t)
    (hshift : relativeProfile mu (Ordinal.log Ordinal.omega0 (thickBlock P a q)) <
      relativeProfile nu (Ordinal.log Ordinal.omega0 (thickBlock P a q))) :
    ∃ i : Nat,
      actualLimitPart (relativeState f (mu+thickBlock P a q) mu t i) ≠
        actualLimitPart (relativeState f (nu+thickBlock P a q) nu t i) ∧
      thickBlock P a (q-2) ≤ actualLimitPart (relativeState f (mu+thickBlock P a q) mu t i) ∧
      thickBlock P a (q-2) ≤ actualLimitPart (relativeState f (nu+thickBlock P a q) nu t i) := by
  let rho := thickBlock P a q
  let rho1 := thickBlock P a (q-1)
  let rho2 := thickBlock P a (q-2)
  let c := relativeProfile mu (if P=0 then a else Ordinal.log Ordinal.omega0 P)
  let d := relativeProfile nu (if P=0 then a else Ordinal.log Ordinal.omega0 P)
  let M := initialLcm (R+1)
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) h2
  have hq0 : 0 < q := by omega
  have hq1 : 0 < q-1 := by omega
  have hq2 : 0 < q-2 := by omega
  have hr : rho < epsilonZero := thick_block_below P a q hP ha
  have hr1 : rho1 < epsilonZero := thick_block_below P a (q-1) hP ha
  have hr2 : rho2 < epsilonZero := thick_block_below P a (q-2) hP ha
  have hrl := thick_block_limit P a q hapos hq0
  have hr1l := thick_block_limit P a (q-1) hapos hq1
  have hr2l := thick_block_limit P a (q-2) hapos hq2
  have hr10 : rho1 < rho := thick_block_strict P a (by omega)
  have hr21 : rho2 ≤ rho1 := thick_block_mono P a (by omega)
  have hr01 : rho=rho1+Ordinal.omega0^a := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ q by omega)] using thick_block_succ P a (q-1)
  have hr12 : rho1=rho2+Ordinal.omega0^a := by
    have h := thick_block_succ P a (q-2)
    rw [show q-2+1=q-1 by omega] at h
    exact h
  have hNa := thick_exponent_norm a ha h2
  have hdrop := thick_head_drop mu P a (q-1) hmu hP ha hq1 hd
  have hdrop' := thick_head_drop nu P a (q-1) hnu hP ha hq1 hd
  rw [Nat.sub_add_cancel (show 1 ≤ q by omega)] at hdrop hdrop'
  change actualOrdinalNorm (mu+rho) ≤ t at hhead
  change actualOrdinalNorm (nu+rho) ≤ t at hhead'
  change actualOrdinalNorm (mu+rho)=actualOrdinalNorm (mu+rho1)+(1+actualOrdinalNorm a) at hdrop
  change actualOrdinalNorm (nu+rho)=actualOrdinalNorm (nu+rho1)+(1+actualOrdinalNorm a) at hdrop'
  have htM : M ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htB : B ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have ht2 : 2 ≤ t := by
    have hp : 0 < (R+2)^4 := pow_pos (by omega) _
    have hb : 100*(R+2)^4 ≤ t := (le_max_left _ _).trans ht
    omega
  have hM := (thick_lcm_bounds R).1
  have hRM := (thick_lcm_bounds R).2
  have hcR : c ≤ R := (relativePrefixNorm mu _ hmu).2.2.trans hmuR
  have hdR : d ≤ R := (relativePrefixNorm nu _ hnu).2.2.trans hnuR
  have hcd : c < d := by
    simpa only [thick_block_leading P a q hq0 hd] using hshift
  have hhead1 : actualOrdinalNorm (mu+rho1)+3 ≤ t := by clear * - hdrop hhead hNa; omega
  have hhead1' : actualOrdinalNorm (nu+rho1)+3 ≤ t := by clear * - hdrop' hhead' hNa; omega
  obtain ⟨i,j,hi,hj,hEi,hEj,hguard,hguard',hreset,hdiverge⟩ := synchronizedTargetVisits f B hf
    mu nu rho rho1 t hmu hnu hr hr1 hmud hnud hrl hr1l hr10.le (max_le ht2 (max_le hhead (max_le hhead' (max_le (by clear * - hhead1; omega) (by clear * - hhead1'; omega)))))
  by_cases hij : i=j
  · subst j
    let E := f^[i] t
    let u := f E
    let n := actualOrdinalNorm rho1
    let pn := actualOrdinalNorm rho2
    let X := u-c-pn
    have hT := epsilonZero_add_principal hmu hr1
    have hT' := epsilonZero_add_principal hnu hr1
    have hA := epsilonZero_add_principal hmu hr
    have hA' := epsilonZero_add_principal hnu hr
    have hAl := Ordinal.isSuccLimit_add mu hrl
    have hAl' := Ordinal.isSuccLimit_add nu hrl
    have hTl := Ordinal.isSuccLimit_add mu hr1l
    have hTl' := Ordinal.isSuccLimit_add nu hr1l
    have hbar : mu+rho1+Ordinal.omega0^(2 : Ordinal) ≤ mu+rho := by
      rw [hr01,← add_assoc]
      exact (add_le_add_iff_left (mu+rho1)).mpr ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone h2)
    have hbar' : nu+rho1+Ordinal.omega0^(2 : Ordinal) ≤ nu+rho := by
      rw [hr01,← add_assoc]
      exact (add_le_add_iff_left (nu+rho1)).mpr ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone h2)
    have hres := long_residue_at f B hf M (mu+rho) (mu+rho1) t i hM hA hAl hTl hbar (max_le hhead (max_le hhead1 (max_le htM htB))) hi
    have hres' := long_residue_at f B hf M (nu+rho) (nu+rho1) t i hM hA' hAl' hTl' hbar' (max_le hhead' (max_le hhead1' (max_le htM htB))) hj
    have hnorm1 : actualOrdinalNorm (mu+rho1)=n+c := by
      rw [thick_head_norm mu P a (q-1) hmu hP ha hq1 hd]
      dsimp [n,rho1,c]
      rw [thick_block_norm P a (q-1) hP ha hd]
    have hnorm1' : actualOrdinalNorm (nu+rho1)=n+d := by
      rw [thick_head_norm nu P a (q-1) hnu hP ha hq1 hd]
      dsimp [n,rho1,d]
      rw [thick_block_norm P a (q-1) hP ha hd]
    rw [hnorm1] at hres
    rw [hnorm1'] at hres'
    have hround := equal_entry_rounded_mod M (potential t) i c d n hres.1 hres'.1
    obtain ⟨hdc,hodd⟩ := rounded_charge_rigidity n c d R M hcd hdR hRM hround
    have hNE : n+d ≤ E := by
      rw [← hnorm1']
      exact entry_norm_ge_target f _ _ i E hT' hj hEj
    have hEt : t ≤ E := iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t
    have hEu : E < u := selected_strict_expand f B hf E
    have hiPos : 0 < i := proper_entry_pos f (mu+rho) (mu+rho1) t i hAl
      ((add_lt_add_iff_left mu).mpr hr10) hi
    have heven : 2 ∣ E := by
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hiPos.ne'
      dsimp [E]
      rw [hk,Function.iterate_succ_apply']
      exact selected_even f B hf _
    have hn : n=pn+(1+actualOrdinalNorm a) := by
      have h := thick_head_drop 0 P a (q-2) zero_lt_epsilonZero hP ha hq2 hd
      rw [show q-2+1=q-1 by omega] at h
      simpa only [zero_add] using h
    have hX : actualOrdinalNorm a+3 ≤ X := by dsimp [X]; omega
    have hpaid : c+pn ≤ u := by omega
    have hentry : Int.ModEq (2*(M : Int)) (E : Int) (2*(((n+c+1)/2 : Nat) : Int)) := by
      rw [← hEi]
      exact hres.2
    have hmod := moving_local_residue f B hf M E c n (actualOrdinalNorm a) hM
      (by omega) heven hodd hentry pn hn hpaid
    have hNaM : actualOrdinalNorm a ∣ M := dvd_initialLcm (by omega) (by omega)
    have hsep := resonant_local_separation rho2 a M X hr2 ha h2 hX hNaM hmod
    have hc2 : relativeProfile mu (Ordinal.log Ordinal.omega0 rho2)=c := by
      rw [thick_block_leading P a (q-2) hq2 hd]
    have hd2 : relativeProfile nu (Ordinal.log Ordinal.omega0 rho2)=d := by
      rw [thick_block_leading P a (q-2) hq2 hd]
    have hlocal := retainedLocalPhase mu rho2 a u hmu hr2 ha (thick_block_positive P a (q-2) hq2)
      hapos (thick_block_divisible P a (q-2) hd) (by omega) (by rw [hc2]; change c+pn<u; omega)
    have hlocal' := retainedLocalPhase nu rho2 a u hnu hr2 ha (thick_block_positive P a (q-2) hq2)
      hapos (thick_block_divisible P a (q-2) hd) (by omega) (by rw [hd2]; change d+pn<u; omega)
    rw [← hr12,hc2] at hlocal
    rw [← hr12,hd2] at hlocal'
    have hY : u-d-pn=X-1 := by dsimp [X]; omega
    have hnext : relativeState f (mu+rho) mu t (i+1)=rho2+actualMaximumPredecessor (Ordinal.omega0^a) X := by
      exact (target_next_relative f _ mu rho1 i E hr1l hi hEi).trans hlocal
    have hnext' : relativeState f (nu+rho) nu t (i+1)=rho2+actualMaximumPredecessor (Ordinal.omega0^a) (X-1) := by
      rw [hY] at hlocal'
      exact (target_next_relative f _ nu rho1 i E hr1l hj hEj).trans hlocal'
    refine ⟨i+1, ?_, ?_, ?_⟩
    · rw [hnext,hnext']
      exact hsep
    · rw [hnext]
      have h := actualLimitPartMonotone (show rho2 ≤ rho2+actualMaximumPredecessor (Ordinal.omega0^a) X from le_self_add)
      have he : actualLimitPart rho2=rho2 := by simpa using limitPart_tail rho2 hr2l 0
      rwa [he] at h
    · rw [hnext']
      have h := actualLimitPartMonotone (show rho2 ≤ rho2+actualMaximumPredecessor (Ordinal.omega0^a) (X-1) from le_self_add)
      have he : actualLimitPart rho2=rho2 := by simpa using limitPart_tail rho2 hr2l 0
      rwa [he] at h
  · obtain ⟨h,hh,hne,hlo,hlo'⟩ := hdiverge hij
    exact ⟨h,hne,hr21.trans hlo,hr21.trans hlo'⟩

end LogicLineages.PermittedControl
