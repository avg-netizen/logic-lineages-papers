module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryProof
open DominantBoundary

private theorem positive_boundary (a target n : Nat) (ha : 0 < a) (hn : 0 < n) :
    positiveCrossing a target ≤ n ↔ target ≤ a * Phi n := by
  rcases SnyatkovInverse.Proof.originalOrderAndRoundTrips with ⟨_, _, _, _, _, _, horder⟩
  have hi := (horder ((target - 1) / a) n hn).1
  have hs : positiveCrossing a target ≤ n ↔ (target - 1) / a < Phi n := by
    unfold positiveCrossing
    omega
  rw [hs]
  have hd : (target - 1) / a < Phi n ↔ target - 1 < a * Phi n := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul ha :
      (target - 1) / a < Phi n ↔ target - 1 < Phi n * a)
  rw [hd]
  have hp : 0 < a * Phi n := Nat.mul_pos ha ((Nat.zero_le n).trans_lt (self_lt_Phi n))
  omega

theorem actualScaledBoundary : DominantBoundaryTargets.ActualScaledBoundary := by
  intro a target n ha
  by_cases hn : n = 0
  · subst n
    simp [positiveCrossing]
  · simpa only [hn, false_and, false_or] using
      (positive_boundary a target n ha (by omega)).symm

private theorem triple_two (n : Nat) : 3 * Phi n ≤ Phi (n + 2) := by
  have h₁ := fullFastControlHierarchyGrowth.2.2 0 n (Nat.zero_le n)
  have h₂ := fullFastControlHierarchyGrowth.2.2 0 (n + 1) (Nat.zero_le (n + 1))
  simp only [Nat.zero_add] at h₁ h₂
  have hadd : n + 1 + 1 = n + 2 := by omega
  rw [hadd] at h₂
  have hm := Nat.mul_le_mul_left 2 h₁
  omega

theorem region_meaning (i a : Nat) (shift : Int) (lower upper : Term) (ν : Nat → Nat) :
    (region i a shift lower upper).eval ν ↔
      (-shift).toNat ≤ ν i ∧
      2 * upper.value ν < 3 * a * Phi ((center a lower).value ν + 1) ∧
      2 * lower.value ν ≤ 3 * a * Phi (((ν i : Int) + shift).toNat) ∧
      a * Phi (((ν i : Int) + shift).toNat) ≤ 2 * upper.value ν := by
  simp only [region, noWide, shiftDomain, atMost, Matrix.eval, Term.value,
    WindowProof.shifted_value, not_lt]

theorem actualFiniteBand : DominantBoundaryTargets.ActualFiniteBand := by
  intro i a shift lower upper ha ν hregion
  obtain ⟨_, hwide, hlo, hhi⟩ := (region_meaning i a shift lower upper ν).mp hregion
  let c := (center a lower).value ν
  let y := ((ν i : Int) + shift).toNat
  change 2 * upper.value ν < 3 * a * Phi (c + 1) at hwide
  change 2 * lower.value ν ≤ 3 * a * Phi y at hlo
  change a * Phi y ≤ 2 * upper.value ν at hhi
  rw [Nat.mul_assoc] at hwide hlo
  have hc : c = positiveCrossing a (2 * lower.value ν) := rfl
  have hlow : c - 2 ≤ y := by
    by_contra h
    have hyc : y + 2 < c := by omega
    have hboundary := positive_boundary a (2 * lower.value ν) (y + 2) ha (by omega)
    rw [← hc] at hboundary
    have hsmall : a * Phi (y + 2) < 2 * lower.value ν := by omega
    have hg : 3 * (a * Phi y) ≤ a * Phi (y + 2) := by
      calc
        3 * (a * Phi y) = a * (3 * Phi y) := by ac_rfl
        _ ≤ a * Phi (y + 2) := Nat.mul_le_mul_left a (triple_two y)
    exact (not_le_of_gt hsmall) (hlo.trans hg)
  have hupp : y ≤ c + 2 := by
    by_contra h
    have hyc : c + 3 ≤ y := by omega
    have htriple := triple_two (c + 1)
    have hadd : c + 1 + 2 = c + 3 := by omega
    rw [hadd] at htriple
    have hg : 3 * (a * Phi (c + 1)) ≤ a * Phi (c + 3) := by
      calc
        3 * (a * Phi (c + 1)) = a * (3 * Phi (c + 1)) := by ac_rfl
        _ ≤ a * Phi (c + 3) := Nat.mul_le_mul_left a htriple
    have hm := Nat.mul_le_mul_left a (Phi_strictMono.monotone hyc)
    exact (not_lt_of_ge hhi) (hwide.trans_le (hg.trans hm))
  exact ⟨hlow, hupp⟩

theorem project_meaning (i a : Nat) (shift : Int) (lower upper : Term) (p : Matrix)
    (ν : Nat → Nat) :
    (project i a shift lower upper p).eval ν ↔
      ∃ d : Nat, d < 5 ∧
        (Matrix.conjunction (region i a shift lower upper) p).eval
          (Function.update ν i ((replacement a lower shift d).value ν)) := by
  rw [project, WindowProof.any_truth]
  constructor
  · rintro ⟨q, hq, hqeval⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact ⟨d, List.mem_range.mp hd, (WindowProof.matrix_substitution _ _ _ _).mp hqeval⟩
  · rintro ⟨d, hd, h⟩
    refine ⟨_, List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩, ?_⟩
    exact (WindowProof.matrix_substitution _ _ _ _).mpr h

theorem actualNonlinearProjection : DominantBoundaryTargets.ActualNonlinearProjection := by
  intro i a shift lower upper p ha hlow hupp ν
  constructor
  · rintro ⟨n, hregion, hp⟩
    have hband := actualFiniteBand i a shift lower upper ha (Function.update ν i n) hregion
    have hcenter : (center a lower).value (Function.update ν i n) = (center a lower).value ν := by
      exact WindowProof.term_update _ i n ν (by simpa [center, Term.variables] using hlow)
    simp only [Function.update_self] at hband
    rw [hcenter] at hband
    let y := ((n : Int) + shift).toNat
    let d := y - ((center a lower).value ν - 2)
    have hd : d < 5 := by dsimp only [d, y]; omega
    have hy : (argumentCandidate a lower d).value ν = y := by
      change ((center a lower).value ν - 2) + d = y
      dsimp only [d, y]
      omega
    have hdom := ((region_meaning i a shift lower upper _).mp hregion).1
    simp only [Function.update_self] at hdom
    have hr : (replacement a lower shift d).value ν = n := by
      rw [replacement, WindowProof.shifted_value, hy]
      dsimp only [y]
      omega
    apply (project_meaning i a shift lower upper p ν).mpr
    refine ⟨d, hd, ?_⟩
    rw [hr]
    exact ⟨hregion, hp⟩
  · intro h
    obtain ⟨d, _, h⟩ := (project_meaning i a shift lower upper p ν).mp h
    exact ⟨_, h⟩

theorem exactParameterSupport : DominantBoundaryTargets.ExactParameterSupport := by
  intro i a shift lower upper p hlow hupp j hj
  rw [project, WindowProof.any_support] at hj
  obtain ⟨q, hq, hj⟩ := hj
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
  have hs := (WindowProof.matrix_support (Matrix.conjunction (region i a shift lower upper) p)
    (replacement a lower shift d) i j).mp hj
  have hregion : j ∈ (region i a shift lower upper).variables →
      j = i ∨ j ∈ lower.variables ∨ j ∈ upper.variables := by
    simp only [region, noWide, center, shiftDomain, atMost, shiftTerm,
      Matrix.variables, Term.variables, List.mem_append, List.mem_singleton, List.not_mem_nil]
    tauto
  have hrepl : j ∈ (replacement a lower shift d).variables ↔ j ∈ lower.variables := by
    simp [replacement, argumentCandidate, center, shiftTerm, Term.variables]
  rcases hs with ⟨hjp, hne⟩ | ⟨_, hjr⟩
  · rcases List.mem_append.mp hjp with hjregion | hjp
    · rcases hregion hjregion with he | hparam
      · exact False.elim (hne he)
      · exact ⟨hne, hparam.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))⟩
    · exact ⟨hne, Or.inr (Or.inr hjp)⟩
  · have hparam := hrepl.mp hjr
    exact ⟨by intro he; subst j; exact hlow hparam, Or.inl hparam⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundaryProof
