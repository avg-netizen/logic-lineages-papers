module
public import LogicLineages.PermittedControl.TailGrowthTargets
public import LogicLineages.PermittedControl.GapInputFoundationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

 theorem terminal_zero_firstEntry (f : Nat → Nat) (a : Ordinal.{0})
    (ha : a < epsilonZero) : FirstEntry f a 0 (terminalWith f a).2 := by
  have hs := terminal_firstFinite f a ha
  refine ⟨zero_le _, ?_, ?_⟩
  · rw [hs.1, zero_add]
    exact Ordinal.natCast_lt_omega0 _
  · intro j hj hh
    exact (not_lt_of_ge (hs.2 j hj)) (by simpa only [zero_add] using hh.2)

 theorem fixed_head_count_monotone (f : Nat → Nat) (B : Nat)
    (hf : SelectedWithThreshold f B) (lam : Ordinal.{0})
    (ha : lam < epsilonZero) (hl : Order.IsSuccLimit lam) (t u : Nat)
    (ht : actualOrdinalNorm lam ≤ t) (htu : t ≤ u) :
    completeCount f lam t ≤ completeCount f lam u := by
  have had := selected_threshold_admissible f B hf
  have hN := nonfinite_norm lam ha (Ordinal.omega0_le_of_isSuccLimit hl)
  have hi := count_initial_facts lam t ha hl ht
  have hj := count_initial_facts lam u ha hl (ht.trans htu)
  have hzero : actualOrdinalNorm (0 : Ordinal) = 0 :=
    (ParametricActualCollapse.Proof.natural_facts 0).2
  have hc := countLag f f B B hf hf lam 0 lam 0 t u
    (completeCount f lam t) (completeCount f lam u) 0 0 ha ha hl hl
    (Or.inl rfl) (Or.inl rfl) hl.pos hl.pos
    (by rw [hzero]; omega) (by rw [hzero]; omega)
    (by rw [hzero]) (by rw [hzero])
    (terminal_zero_firstEntry f _ hi.1) (terminal_zero_firstEntry f _ hj.1)
  have he : actualLimitPart (relativeState f lam 0 t 0) = lam := by
    simpa only [relativeState, Function.iterate_zero_apply, Ordinal.sub_zero, countInitial] using limitPart_tail lam hl (t-actualOrdinalNorm lam)
  have he' : actualLimitPart (relativeState f lam 0 u 0) = lam := by
    simpa only [relativeState, Function.iterate_zero_apply, Ordinal.sub_zero, countInitial] using limitPart_tail lam hl (u-actualOrdinalNorm lam)
  have hout := hc.2 (by rw [he,he']) (by
    intro i _
    simpa only [Nat.add_zero] using (had.1.iterate (i+1)).monotone htu)
  simpa only [Nat.add_zero] using hout

 theorem two_mul_le_two_power (n : Nat) (hn : 0 < n) : 2*n ≤ 2^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : 2 ≤ 2^(k+1) := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : Nat)) (by omega : 1 ≤ k+1)
      simpa using this
    rw [pow_succ]
    omega

 theorem positive_iterate_double_separation (f : Nat → Nat) (B : Nat)
    (hf : SelectedWithThreshold f B) (t D : Nat) (hD : 0 < D) :
    2^(2^(f^[D] t)) ≤ f^[D] (t+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  have hm := (selected_threshold_admissible f B hf).1
  have hlt : f^[k] t < f^[k] (t+1) := (hm.iterate k) (show t < t+1 by omega)
  have hg := (selected_laws f B hf).2.2.2.1 (f^[k] t)
  have hle := hm.monotone (show f^[k] t+1 ≤ f^[k] (t+1) by omega)
  simpa only [Function.iterate_succ_apply'] using hg.trans hle

 theorem fixedHeadTailGrowth : Targets.FixedHeadTailGrowth := by
  intro f B hf lam ha hl u
  let t := actualOrdinalNorm lam+u
  have ht : actualOrdinalNorm lam ≤ t := by dsimp [t]; omega
  have hi := count_initial_facts lam t ha hl ht
  have hj := count_initial_facts lam (t+1) ha hl (by omega)
  have had := selected_threshold_admissible f B hf
  have hs := terminalSemantics f had.1 had.2 (countInitial lam t) hi.1
  have hs' := terminalSemantics f had.1 had.2 (countInitial lam (t+1)) hj.1
  let D := (terminalWith f (countInitial lam t)).2
  let D' := (terminalWith f (countInitial lam (t+1))).2
  let Z := (terminalWith f (countInitial lam t)).1
  let Z' := (terminalWith f (countInitial lam (t+1))).1
  have hp : 0 < D ∧ D < Z := hs.2.2.2.2 hi.2.2
  have hd : D ≤ D' := fixed_head_count_monotone f B hf lam ha hl t (t+1) ht (by omega)
  have hz : Z=f^[D] t := by simpa only [hi.2.1] using hs.2.2.2.1
  have hz' : Z'=f^[D'] (t+1) := by simpa only [hj.2.1] using hs'.2.2.2.1
  have hsep : 2^(2^Z) ≤ Z' := by
    rw [hz,hz']
    exact (positive_iterate_double_separation f B hf t D hp.1).trans
      ((had.1.monotone.monotone_iterate_of_le_map (control_self_le f had.2 (t+1))) hd)
  have he : Z+D < 2^Z := lt_of_lt_of_le (by omega) (two_mul_le_two_power Z (by omega))
  have hpow : 2^(Z+D) < 2^(2^Z) := Nat.pow_lt_pow_right (by omega) he
  have hout : 2^collapseWith f (countInitial lam t) < collapseWith f (countInitial lam (t+1)) := by
    rw [hs.2.2.1,hs'.2.2.1]
    exact lt_of_lt_of_le (hpow.trans_le hsep) (Nat.le_add_right _ _)
  have hc : countInitial lam t = lam+(u : Ordinal) := by
    simp only [countInitial,t,Nat.add_sub_cancel_left]
  have hc' : countInitial lam (t+1) = lam+((u+1 : Nat) : Ordinal) := by
    simp only [countInitial,t, Nat.add_assoc,Nat.add_sub_cancel_left]
  rwa [hc,hc'] at hout

 theorem fullTailGrowth : Targets.FullTailGrowth := by
  refine ⟨fixedHeadTailGrowth, ?_, ?_⟩
  · exact fixedHeadTailGrowth factorialControl 0 (Or.inl ⟨rfl,rfl⟩)
  · intro b
    exact fixedHeadTailGrowth (nearControl b) (b+1) (Or.inr ⟨b,rfl,rfl⟩)

end LogicLineages.PermittedControl
