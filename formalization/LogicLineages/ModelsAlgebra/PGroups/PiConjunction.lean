module

public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranches
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem positive_complexity_monotone : Targets.groupPositiveComplexityMonotone.{v} := by
  intro side α β n φ hα hle h
  have hβ : β ≠ 0 := by
    intro hz
    subst β
    exact hα (le_antisymm hle bot_le)
  cases h with
  | qf side q => exact (hα rfl).elim
  | sigma positive s m matrix γ lower rank =>
    exact Complexity.sigma hβ s m matrix γ (fun i => (lower i).trans_le hle) rank
  | pi positive s m matrix γ lower rank =>
    exact Complexity.pi hβ s m matrix γ (fun i => (lower i).trans_le hle) rank

theorem pi_one_normalization_realization : Targets.groupPiOneNormalizationRealization.{u} := by
  intro G _ n φ a
  cases φ with
  | qf q => exact (pi_qf_padding.{u,0} 1 one_ne_zero n q).2 G a
  | disjEx s m matrix => exact Iff.rfl
  | conjAll s m matrix => exact Iff.rfl

theorem pi_one_normalization_complexity : Targets.groupPiOneNormalizationComplexity.{v} := by
  intro γ hγ n φ h
  cases h with
  | qf side q => exact (pi_qf_padding.{0,v} 1 one_ne_zero n q).1
  | pi positive s m matrix β lower rank =>
    exact positive_complexity_monotone .pi γ 1 n (.conjAll s m matrix)
      positive (Order.lt_two_iff.mp hγ) (Complexity.pi positive s m matrix β lower rank)

private theorem append_empty {G : Type u} {n : ℕ} (a : Fin n → G) (d : Fin 0 → G) :
    append a d = a := by
  funext i
  simpa [append] using (Fin.addCases_left (m := n) (n := 0) (motive := fun _ => G)
    (left := a) (right := d) i)

/-- The actual fallback conjunction, also available to later assembly gates. -/
theorem ordinary_conjunction_realization (G : Type u) [AddCommGroup G] {n : ℕ}
    (φ ψ : Formula n) (a : Fin n → G) :
    (ordinaryConjunction φ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  unfold ordinaryConjunction
  rw [countable_conj_all_realization Bool n _ _ G a]
  constructor
  · intro h
    exact ⟨by simpa [append_empty] using h false Fin.elim0,
      by simpa [append_empty] using h true Fin.elim0⟩
  · rintro ⟨hφ, hψ⟩ b d
    cases b
    · simpa [append_empty] using hφ
    · simpa [append_empty] using hψ

theorem pi_conjunction_realization : Targets.groupPiConjunctionRealization.{u} := by
  intro G _ n φ ψ a
  cases φ with
  | qf q =>
    cases ψ <;> exact ordinary_conjunction_realization G _ _ a
  | disjEx s m matrix =>
    cases ψ <;> exact ordinary_conjunction_realization G _ _ a
  | conjAll s m matrix =>
    cases ψ with
    | qf q => exact ordinary_conjunction_realization G _ _ a
    | disjEx t l other => exact ordinary_conjunction_realization G _ _ a
    | conjAll t l other =>
      unfold piConjunction
      rw [countable_conj_all_realization (s ⊕ t) n _ _ G a]
      constructor
      · intro h
        exact ⟨fun i d => h (.inl i) d, fun i d => h (.inr i) d⟩
      · rintro ⟨hφ, hψ⟩ k
        cases k with
        | inl i => exact hφ i
        | inr i => exact hψ i

theorem pi_conjunction_complexity : Targets.groupPiConjunctionComplexity.{v} := by
  intro α hα n φ ψ hφ hψ
  cases hφ with
  | qf side q => exact (hα rfl).elim
  | pi positive s m matrix β lower rank =>
    cases hψ with
    | qf side q => exact (hα rfl).elim
    | pi positive' t l other γ lower' rank' =>
      apply countable_conj_all_complexity α hα (s ⊕ t) n (Sum.elim m l)
        (fun k => match k with | .inl i => matrix i | .inr i => other i) (Sum.elim β γ)
      · intro k
        cases k with
        | inl i => exact lower i
        | inr i => exact lower' i
      · intro k
        cases k with
        | inl i => exact rank i
        | inr i => exact rank' i

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
