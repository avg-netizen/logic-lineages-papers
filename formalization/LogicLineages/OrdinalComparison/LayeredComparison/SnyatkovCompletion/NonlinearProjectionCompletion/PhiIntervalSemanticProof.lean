module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundarySemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalProof
open PhiInterval

theorem actualLowerBoundary : PhiIntervalTargets.ActualLowerBoundary := by
  intro a shift target n ha
  by_cases hfirst : target ≤ a * Phi shift.toNat
  · simp only [lowerBound, if_pos hfirst]
    constructor
    · rintro ⟨hd, _⟩
      omega
    · intro hn
      have hd : 0 ≤ (n : Int) + shift := by omega
      have harg : shift.toNat ≤ ((n : Int) + shift).toNat := by omega
      exact ⟨hd, hfirst.trans (Nat.mul_le_mul_left a (Phi_strictMono.monotone harg))⟩
  · simp only [lowerBound, if_neg hfirst]
    let c := DominantBoundary.positiveCrossing a target
    have hc : shift.toNat < c := by
      by_contra h
      have hcle : c ≤ shift.toNat := by omega
      exact hfirst ((DominantBoundaryProof.actualScaledBoundary a target shift.toNat ha).mpr
        (Or.inr hcle))
    have hzero : ¬target ≤ a * Phi 0 := by
      intro hz
      exact hfirst (hz.trans (Nat.mul_le_mul_left a
        (Phi_strictMono.monotone (Nat.zero_le shift.toNat))))
    have hcross (y : Nat) : target ≤ a * Phi y ↔ c ≤ y := by
      rw [DominantBoundaryProof.actualScaledBoundary a target y ha]
      constructor
      · rintro (⟨hy, ht⟩ | hcy)
        · subst y
          exact False.elim (hzero ht)
        · exact hcy
      · exact Or.inr
    change (0 ≤ (n : Int) + shift ∧ target ≤ a * Phi (((n : Int) + shift).toNat)) ↔
      ((c : Int) - shift).toNat ≤ n
    constructor
    · rintro ⟨hd, ht⟩
      have hcy := (hcross _).mp ht
      omega
    · intro hn
      refine ⟨?_, (hcross _).mpr ?_⟩ <;> omega

theorem actualResidueRepresentative : PhiIntervalTargets.ActualResidueRepresentative := by
  intro m start residue n hm hstart hresidue
  let d := (n - start) % m
  have hd : d < m := Nat.mod_lt _ hm
  have hdn : d ≤ n - start := Nat.mod_le _ _
  refine ⟨d, hd, by omega, ?_⟩
  have hn : start + (n - start) = n := by omega
  calc
    (start + d) % m = (start + (n - start)) % m := by
      dsimp only [d]
      simp only [Nat.add_mod, Nat.mod_mod]
    _ = n % m := congrArg (fun k : Nat => k % m) hn
    _ = residue % m := hresidue

theorem residue_value (m : Nat) (t : Term) (ν : Nat → Nat) :
    (residueTerm m t).value ν = t.value ν % m := by
  change t.value ν - m * (t.value ν / m) = t.value ν % m
  have h := Nat.mod_add_div (t.value ν) m
  omega

theorem interval_meaning (i a : Nat) (shift : Int) (m : Nat) (lower upper residue : Term)
    (ν : Nat → Nat) :
    (interval i a shift m lower upper residue).eval ν ↔
      (-shift).toNat ≤ ν i ∧
      lower.value ν ≤ a * Phi (((ν i : Int) + shift).toNat) ∧
      a * Phi (((ν i : Int) + shift).toNat) ≤ upper.value ν ∧
      ν i % m = residue.value ν % m := by
  simp only [interval, Matrix.eval, shiftDomain, atMost, residue_value,
    Term.value, WindowProof.shifted_value, not_lt]

theorem fromStart_meaning (i a : Nat) (shift : Int) (m : Nat) (lower upper residue start : Term)
    (ν : Nat → Nat) :
    (fromStart i a shift m lower upper residue start).eval ν ↔
      ∃ d : Nat, d < m ∧ (interval i a shift m lower upper residue).eval
        (Function.update ν i (start.value ν + d)) := by
  rw [fromStart, WindowProof.any_truth]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact ⟨d, List.mem_range.mp hd, (WindowProof.matrix_substitution _ _ _ _).mp h⟩
  · rintro ⟨d, hd, h⟩
    refine ⟨_, List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩, ?_⟩
    exact (WindowProof.matrix_substitution _ _ _ _).mpr h

theorem fromStart_projection (i a : Nat) (shift : Int) (m : Nat) (lower upper residue start : Term)
    (ha : 0 < a) (hm : 0 < m) (hlow : i ∉ lower.variables) (hupp : i ∉ upper.variables)
    (hres : i ∉ residue.variables) (ν : Nat → Nat)
    (hstart : start.value ν = lowerBound a shift (lower.value ν)) :
    (fromStart i a shift m lower upper residue start).eval ν ↔
      ∃ n : Nat, (interval i a shift m lower upper residue).eval (Function.update ν i n) := by
  constructor
  · intro h
    obtain ⟨d, _, h⟩ := (fromStart_meaning i a shift m lower upper residue start ν).mp h
    exact ⟨_, h⟩
  · rintro ⟨n, hn⟩
    have hv := (interval_meaning i a shift m lower upper residue _).mp hn
    have hl := WindowProof.term_update lower i n ν hlow
    have hu := WindowProof.term_update upper i n ν hupp
    have hr := WindowProof.term_update residue i n ν hres
    simp only [Function.update_self, hl, hu, hr] at hv
    have hbound : lowerBound a shift (lower.value ν) ≤ n :=
      (actualLowerBoundary a shift (lower.value ν) n ha).mp ⟨by omega, hv.2.1⟩
    have hstartn : start.value ν ≤ n := by rw [hstart]; exact hbound
    obtain ⟨d, hd, hsmall, hmod⟩ :=
      actualResidueRepresentative m (start.value ν) (residue.value ν) n hm hstartn hv.2.2.2
    have hnewbound : lowerBound a shift (lower.value ν) ≤ start.value ν + d := by
      rw [← hstart]
      omega
    obtain ⟨hnewdom, hnewlo⟩ :=
      (actualLowerBoundary a shift (lower.value ν) (start.value ν + d) ha).mpr hnewbound
    have harg : (((start.value ν + d : Nat) : Int) + shift).toNat ≤
        ((n : Int) + shift).toNat := by omega
    have hnewhi := (Nat.mul_le_mul_left a (Phi_strictMono.monotone harg)).trans hv.2.2.1
    apply (fromStart_meaning i a shift m lower upper residue start ν).mpr
    refine ⟨d, hd, (interval_meaning i a shift m lower upper residue _).mpr ?_⟩
    have hl' := WindowProof.term_update lower i (start.value ν + d) ν hlow
    have hu' := WindowProof.term_update upper i (start.value ν + d) ν hupp
    have hr' := WindowProof.term_update residue i (start.value ν + d) ν hres
    simp only [Function.update_self, hl', hu', hr']
    exact ⟨by omega, hnewlo, hnewhi, hmod⟩

theorem initialGuard_meaning (a : Nat) (shift : Int) (lower : Term) (ν : Nat → Nat) :
    (initialGuard a shift lower).eval ν ↔ lower.value ν ≤ a * Phi shift.toNat := by
  simp only [initialGuard, atMost, Matrix.eval, Term.value, not_lt]

theorem actualNonlinearProjection : PhiIntervalTargets.ActualNonlinearProjection := by
  intro i a shift m lower upper residue ha hm hlow hupp hres ν
  symm
  change ((initialGuard a shift lower).eval ν ∧
      (fromStart i a shift m lower upper residue (initialStart shift)).eval ν) ∨
    (¬(initialGuard a shift lower).eval ν ∧
      (fromStart i a shift m lower upper residue (tailStart a shift lower)).eval ν) ↔ _
  rw [initialGuard_meaning]
  by_cases hfirst : lower.value ν ≤ a * Phi shift.toNat
  · simp only [hfirst, true_and, not_true_eq_false, false_and, or_false]
    apply fromStart_projection i a shift m lower upper residue (initialStart shift) ha hm hlow hupp hres ν
    simp only [initialStart, Term.value, lowerBound, if_pos hfirst]
  · simp only [hfirst, false_and, not_false_eq_true, true_and, false_or]
    apply fromStart_projection i a shift m lower upper residue (tailStart a shift lower) ha hm hlow hupp hres ν
    rw [tailStart, WindowProof.shifted_value]
    simp only [crossingTerm, Term.value, lowerBound, if_neg hfirst,
      DominantBoundary.positiveCrossing, sub_eq_add_neg]

private theorem fromStart_support (i a : Nat) (shift : Int) (m : Nat) (lower upper residue start : Term)
    (hlow : i ∉ lower.variables) (hstart : ∀ j ∈ start.variables, j ∈ lower.variables) (j : Nat)
    (hj : j ∈ (fromStart i a shift m lower upper residue start).variables) :
    j ≠ i ∧ (j ∈ lower.variables ∨ j ∈ upper.variables ∨ j ∈ residue.variables) := by
  rw [fromStart, WindowProof.any_support] at hj
  obtain ⟨q, hq, hj⟩ := hj
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
  have hs := (WindowProof.matrix_support (interval i a shift m lower upper residue)
    (.add start (.numeral d)) i j).mp hj
  have hb : j ∈ (interval i a shift m lower upper residue).variables →
      j = i ∨ j ∈ lower.variables ∨ j ∈ upper.variables ∨ j ∈ residue.variables := by
    simp only [interval, residueTerm, shiftDomain, atMost, shiftTerm, Matrix.variables, Term.variables,
      List.mem_append, List.mem_singleton, List.not_mem_nil]
    tauto
  rcases hs with ⟨hjbody, hne⟩ | ⟨_, hjstart⟩
  · rcases hb hjbody with he | hparam
    · exact False.elim (hne he)
    · exact ⟨hne, hparam⟩
  · have hjs : j ∈ start.variables := by simpa [Term.variables] using hjstart
    have hjl := hstart j hjs
    exact ⟨by intro he; subst j; exact hlow hjl, Or.inl hjl⟩

theorem exactParameterSupport : PhiIntervalTargets.ExactParameterSupport := by
  intro i a shift m lower upper residue hlow hupp hres j hj
  have hg : j ∈ (initialGuard a shift lower).variables ↔ j ∈ lower.variables := by
    simp [initialGuard, atMost, Matrix.variables, Term.variables]
  have hguard : j ∈ (initialGuard a shift lower).variables →
      j ≠ i ∧ (j ∈ lower.variables ∨ j ∈ upper.variables ∨ j ∈ residue.variables) := by
    intro h
    have hl := hg.mp h
    exact ⟨by intro he; subst j; exact hlow hl, Or.inl hl⟩
  simp only [project, Matrix.variables, List.mem_append] at hj
  rcases hj with ((h | h) | (h | h))
  · exact hguard h
  · exact fromStart_support i a shift m lower upper residue (initialStart shift) hlow
      (by simp [initialStart, Term.variables]) j h
  · exact hguard h
  · apply fromStart_support i a shift m lower upper residue (tailStart a shift lower) hlow ?_ j h
    intro k hk
    simpa [tailStart, crossingTerm, shiftTerm, Term.variables] using hk

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PhiIntervalProof
