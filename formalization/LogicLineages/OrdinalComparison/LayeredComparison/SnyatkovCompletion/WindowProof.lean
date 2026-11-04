module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollisionProof
public import Mathlib.Tactic.Tauto
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof

private theorem combine_support (A B C D E F : Prop) :
    (((A ∧ E) ∨ (C ∧ F)) ∨ ((B ∧ E) ∨ (D ∧ F))) ↔
      (((A ∨ B) ∧ E) ∨ ((C ∨ D) ∧ F)) := by
  constructor
  · rintro ((⟨ha, he⟩ | ⟨hc, hf⟩) | (⟨hb, he⟩ | ⟨hd, hf⟩))
    · exact Or.inl ⟨Or.inl ha, he⟩
    · exact Or.inr ⟨Or.inl hc, hf⟩
    · exact Or.inl ⟨Or.inr hb, he⟩
    · exact Or.inr ⟨Or.inr hd, hf⟩
  · rintro (⟨ha | hb, he⟩ | ⟨hc | hd, hf⟩)
    · exact Or.inl (Or.inl ⟨ha, he⟩)
    · exact Or.inr (Or.inl ⟨hb, he⟩)
    · exact Or.inl (Or.inr ⟨hc, hf⟩)
    · exact Or.inr (Or.inr ⟨hd, hf⟩)

theorem term_substitution (a replacement : Term) (i : Nat) (ν : Nat → Nat) :
    (a.substitute i replacement).value ν =
      a.value (Function.update ν i (replacement.value ν)) := by
  induction a with
  | numeral n => rfl
  | «variable» j =>
    by_cases h : j = i <;> simp [Term.substitute, Term.value, h]
  | add a b ha hb => simp only [Term.substitute, Term.value, ha, hb]
  | subtract a b ha hb => simp only [Term.substitute, Term.value, ha, hb]
  | multiply c a ha => simp only [Term.substitute, Term.value, ha]
  | divide c a ha => simp only [Term.substitute, Term.value, ha]
  | phi a ha => simp only [Term.substitute, Term.value, ha]
  | hyper a ha => simp only [Term.substitute, Term.value, ha]
  | phiInverse a ha => simp only [Term.substitute, Term.value, ha]
  | hyperInverse a ha => simp only [Term.substitute, Term.value, ha]

theorem matrix_substitution (p : Matrix) (replacement : Term) (i : Nat) (ν : Nat → Nat) :
    (p.substitute i replacement).eval ν ↔
      p.eval (Function.update ν i (replacement.value ν)) := by
  induction p <;> simp_all only [Matrix.substitute, Matrix.eval, term_substitution]

theorem exactSubstitution : WindowTargets.ExactSubstitution :=
  ⟨term_substitution, matrix_substitution⟩

theorem term_update (a : Term) (i n : Nat) (ν : Nat → Nat)
    (hi : i ∉ a.variables) : a.value (Function.update ν i n) = a.value ν := by
  induction a <;>
    simp_all [Term.variables, Term.value, ne_comm]

theorem actualArgumentWindow : WindowTargets.ActualArgumentWindow := by
  intro a b c hlo hhi
  have hba : b ≤ a := Phi_strictMono.le_iff_le.mp hlo
  have hab := SnyatkovHyperCollision.Proof.actualCoefficientElimination a b c hhi
  exact ⟨a - b, by omega, by omega⟩

theorem shifted_value (a : Term) (e : Int) (ν : Nat → Nat) :
    (shiftTerm a e).value ν = ((a.value ν : Int) + e).toNat := by
  cases e <;> simp only [shiftTerm, Term.value] <;> omega

theorem close_truth (i : Nat) (a : Term) (e : Int) (c : Nat) (ν : Nat → Nat) :
    (closeMatrix i a e c).eval ν ↔
      0 ≤ (ν i : Int) + e ∧
      Phi (a.value ν) ≤ Phi (((ν i : Int) + e).toNat) ∧
      Phi (((ν i : Int) + e).toNat) ≤ c * Phi (a.value ν) := by
  simp only [closeMatrix, shiftDomain, atMost, Matrix.eval, shifted_value, Term.value,
    not_lt]
  have h : (-e).toNat ≤ ν i ↔ 0 ≤ (ν i : Int) + e := by omega
  rw [h]

theorem any_truth (xs : List Matrix) (ν : Nat → Nat) :
    (Matrix.any xs).eval ν ↔ ∃ p ∈ xs, p.eval ν := by
  induction xs with
  | nil => simp [Matrix.any, Matrix.eval]
  | cons p ps ih => simp [Matrix.any, Matrix.eval, ih]

theorem finite_truth (i : Nat) (a : Term) (e : Int) (c : Nat) (p : Matrix)
    (ν : Nat → Nat) :
    (finiteWindow i a e c p).eval ν ↔
      ∃ d : Nat, d ≤ c ∧
        (Matrix.conjunction (closeMatrix i a e c) p).eval
          (Function.update ν i ((replacementTerm a e d).value ν)) := by
  rw [finiteWindow, any_truth]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact ⟨d, by have := List.mem_range.mp hd; omega,
      (matrix_substitution _ _ _ _).mp h⟩
  · rintro ⟨d, hd, h⟩
    refine ⟨_, List.mem_map.mpr ⟨d, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    exact (matrix_substitution _ _ _ _).mpr h

theorem actualFiniteElimination : WindowTargets.ActualFiniteElimination := by
  intro i a e c p hi ν
  constructor
  · rintro ⟨n, hclose, hp⟩
    obtain ⟨hdom, hlo, hhi⟩ := (close_truth i a e c _).mp hclose
    have ha := term_update a i n ν hi
    simp only [Function.update_self] at hdom hlo hhi
    rw [ha] at hlo hhi
    obtain ⟨d, hd, harg⟩ := actualArgumentWindow
      (((n : Int) + e).toNat) (a.value ν) c hlo hhi
    have hr : (replacementTerm a e d).value ν = n := by
      rw [replacementTerm, shifted_value]
      simp only [Term.value]
      omega
    apply (finite_truth i a e c p ν).mpr
    refine ⟨d, hd, ?_⟩
    rw [hr]
    exact ⟨hclose, hp⟩
  · intro h
    obtain ⟨d, hd, h⟩ := (finite_truth i a e c p ν).mp h
    exact ⟨_, h.1, h.2⟩

theorem term_support (a r : Term) (i j : Nat) :
    j ∈ (a.substitute i r).variables ↔
      (j ∈ a.variables ∧ j ≠ i) ∨ (i ∈ a.variables ∧ j ∈ r.variables) := by
  induction a with
  | numeral n => simp [Term.substitute, Term.variables]
  | «variable» k =>
    by_cases h : k = i
    · subst k; simp [Term.substitute, Term.variables]
    · simp only [Term.substitute, if_neg h, Term.variables, List.mem_singleton]
      constructor
      · intro hj
        subst j
        exact Or.inl ⟨rfl, h⟩
      · rintro (⟨hj, _⟩ | ⟨hik, _⟩)
        · exact hj
        · exact False.elim (h hik.symm)
  | add a b ha hb =>
    simp only [Term.substitute, Term.variables, List.mem_append, ha, hb]
    exact combine_support _ _ _ _ _ _
  | subtract a b ha hb =>
    simp only [Term.substitute, Term.variables, List.mem_append, ha, hb]
    exact combine_support _ _ _ _ _ _
  | multiply c a ha => exact ha
  | divide c a ha => exact ha
  | phi a ha => exact ha
  | hyper a ha => exact ha
  | phiInverse a ha => exact ha
  | hyperInverse a ha => exact ha

theorem matrix_support (p : Matrix) (r : Term) (i j : Nat) :
    j ∈ (p.substitute i r).variables ↔
      (j ∈ p.variables ∧ j ≠ i) ∨ (i ∈ p.variables ∧ j ∈ r.variables) := by
  induction p with
  | truth => simp [Matrix.substitute, Matrix.variables]
  | falsity => simp [Matrix.substitute, Matrix.variables]
  | equal a b =>
    simp only [Matrix.substitute, Matrix.variables, List.mem_append, term_support]
    exact combine_support _ _ _ _ _ _
  | less a b =>
    simp only [Matrix.substitute, Matrix.variables, List.mem_append, term_support]
    exact combine_support _ _ _ _ _ _
  | divisible m a => exact term_support a r i j
  | negative p hp => exact hp
  | conjunction p q hp hq =>
    simp only [Matrix.substitute, Matrix.variables, List.mem_append, hp, hq]
    exact combine_support _ _ _ _ _ _
  | disjunction p q hp hq =>
    simp only [Matrix.substitute, Matrix.variables, List.mem_append, hp, hq]
    exact combine_support _ _ _ _ _ _

theorem any_support (xs : List Matrix) (j : Nat) :
    j ∈ (Matrix.any xs).variables ↔ ∃ p ∈ xs, j ∈ p.variables := by
  induction xs with
  | nil => simp [Matrix.any, Matrix.variables]
  | cons p ps ih => simp [Matrix.any, Matrix.variables, ih]

theorem exactWindowSupport : WindowTargets.ExactWindowSupport := by
  intro i a e c p hi j hj
  rw [finiteWindow, any_support] at hj
  obtain ⟨q, hq, hj⟩ := hj
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  have hs := (matrix_support (Matrix.conjunction (closeMatrix i a e c) p)
    (replacementTerm a e d) i j).mp hj
  have hc : j ∈ (closeMatrix i a e c).variables → j = i ∨ j ∈ a.variables := by
    simp only [closeMatrix, shiftDomain, atMost, shiftTerm, Matrix.variables,
      Term.variables, List.mem_append, List.mem_singleton, List.not_mem_nil]
    tauto
  have hr : j ∈ (replacementTerm a e d).variables ↔ j ∈ a.variables := by
    simp [replacementTerm, shiftTerm, Term.variables]
  rcases hs with ⟨hjp, hne⟩ | ⟨_, hjr⟩
  · rcases List.mem_append.mp hjp with hjc | hjp
    · rcases hc hjc with he | hja
      · exact False.elim (hne he)
      · exact ⟨hne, Or.inl hja⟩
    · exact ⟨hne, Or.inr hjp⟩
  · have hja := hr.mp hjr
    exact ⟨by intro he; subst j; exact hi hja, Or.inl hja⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
