module
public import LogicLineages.ModelsAlgebra.PGroups.RawConjunctionTargets
public import LogicLineages.ModelsAlgebra.PGroups.RawSemantics
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

theorem raw_countable_conjunction : Targets.groupRawCountableConjunction.{u} := by
  intro ι _ n m matrix G R a
  let e := branchEquiv ι
  change (∀ k : branchIndices ι, ∀ d : Fin (m (e.symm k)) → G,
    (matrix (e.symm k)).RawRealize R (append a d)) ↔ _
  constructor
  · intro h i
    have hi := h (e i)
    rw [e.symm_apply_apply i] at hi
    exact hi
  · intro h k d
    exact h (e.symm k) d

private theorem append_empty {G : Type u} {n : ℕ} (a : Fin n → G) (d : Fin 0 → G) :
    append a d = a := by
  funext i
  simpa [append] using (Fin.addCases_left (m := n) (n := 0) (motive := fun _ => G)
    (left := a) (right := d) i)

/-- The actual fallback conjunction, also available to later assembly gates. -/
theorem raw_ordinary_conjunction (G : Type u) (R : RawGroupStructure G) {n : ℕ}
    (φ ψ : Formula n) (a : Fin n → G) :
    (ordinaryConjunction φ ψ).RawRealize R a ↔ φ.RawRealize R a ∧ ψ.RawRealize R a := by
  unfold ordinaryConjunction
  rw [raw_countable_conjunction Bool n _ _ G R a]
  constructor
  · intro h
    exact ⟨by simpa [append_empty] using h false Fin.elim0,
      by simpa [append_empty] using h true Fin.elim0⟩
  · rintro ⟨hφ, hψ⟩ b d
    cases b
    · simpa [append_empty] using hφ
    · simpa [append_empty] using hψ

theorem raw_pi_conjunction : Targets.groupRawPiConjunction.{u} := by
  intro n φ ψ G R a
  cases φ with
  | qf q =>
    cases ψ <;> exact raw_ordinary_conjunction G R _ _ a
  | disjEx s m matrix =>
    cases ψ <;> exact raw_ordinary_conjunction G R _ _ a
  | conjAll s m matrix =>
    cases ψ with
    | qf q => exact raw_ordinary_conjunction G R _ _ a
    | disjEx t l other => exact raw_ordinary_conjunction G R _ _ a
    | conjAll t l other =>
      unfold piConjunction
      rw [raw_countable_conjunction (s ⊕ t) n _ _ G R a]
      constructor
      · intro h
        exact ⟨fun i d => h (.inl i) d, fun i d => h (.inr i) d⟩
      · rintro ⟨hφ, hψ⟩ k
        cases k with
        | inl i => exact hφ i
        | inr i => exact hψ i

theorem raw_difference_agreement : Targets.groupRawDifferenceAgreement.{u} := by
  intro G _ n a d
  exact and_congr (raw_formula_agreement G n a d.sigmaPart)
    (raw_formula_agreement G n a d.piPart)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
