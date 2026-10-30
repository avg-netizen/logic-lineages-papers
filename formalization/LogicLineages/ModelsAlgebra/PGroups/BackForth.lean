module

public import LogicLineages.ModelsAlgebra.PGroups.BackForthTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth

universe u v

private theorem data_unfold (α : Ordinal.{v}) : comparisonData.{u} α =
    comparisonStep α (fun β _ => comparisonData β) :=
  WellFounded.fix_eq Ordinal.lt_wf comparisonStep α

theorem zero_comparison : Targets.groupBackForthZero.{u,v} := by
  intro A B _ _ n a b
  unfold BackAndForth
  rw [data_unfold]
  simp [comparisonStep]

theorem positive_comparison : Targets.groupBackForthPositive.{u,v} := by
  intro α hα A B _ _ n a b
  unfold BackAndForth
  rw [data_unfold]
  simp only [comparisonStep, if_neg hα]

theorem term_product_evaluation : Targets.groupTermProductEvaluation.{u} := by
  intro A₁ A₂ _ _ n a₁ a₂ t
  induction t with
  | var i => rfl
  | zero => rfl
  | neg s ih =>
    change -(s.eval (fun i => (a₁ i, a₂ i))) = (-s.eval a₁, -s.eval a₂)
    rw [ih]
    rfl
  | add s t ihs iht =>
    change s.eval (fun i => (a₁ i, a₂ i)) + t.eval (fun i => (a₁ i, a₂ i)) =
      (s.eval a₁ + t.eval a₁, s.eval a₂ + t.eval a₂)
    rw [ihs, iht]
    rfl

private theorem atomic_product {A₁ A₂ B₁ B₂ : Type u}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂]
    {n : ℕ} (a₁ : Fin n → A₁) (a₂ : Fin n → A₂) (b₁ : Fin n → B₁) (b₂ : Fin n → B₂)
    (h₁ : AtomicAgreement a₁ b₁) (h₂ : AtomicAgreement a₂ b₂) :
    AtomicAgreement (fun i => (a₁ i, a₂ i)) (fun i => (b₁ i, b₂ i)) := by
  intro s t
  rw [term_product_evaluation A₁ A₂ n a₁ a₂ s, term_product_evaluation A₁ A₂ n a₁ a₂ t,
    term_product_evaluation B₁ B₂ n b₁ b₂ s, term_product_evaluation B₁ B₂ n b₁ b₂ t,
    Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (h₁ s t) (h₂ s t)

private theorem append_pair {A₁ A₂ : Type u} {n m : ℕ}
    (a₁ : Fin n → A₁) (a₂ : Fin n → A₂) (c₁ : Fin m → A₁) (c₂ : Fin m → A₂) :
    (fun i : Fin (n + m) => ((append a₁ c₁) i, (append a₂ c₂) i)) =
      append (fun i => (a₁ i, a₂ i)) (fun i => (c₁ i, c₂ i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

theorem finite_product_preservation : Targets.groupFiniteProductPreservation.{u,v} := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro A₁ A₂ B₁ B₂ _ _ _ _ n a₁ a₂ b₁ b₂ h₁ h₂
    by_cases hα : α = 0
    · subst α
      rw [zero_comparison A₁ B₁ n a₁ b₁] at h₁
      rw [zero_comparison A₂ B₂ n a₂ b₂] at h₂
      rw [zero_comparison (A₁ × A₂) (B₁ × B₂) n]
      exact atomic_product a₁ a₂ b₁ b₂ h₁ h₂
    · apply (positive_comparison α hα (A₁ × A₂) (B₁ × B₂) n _ _).mpr
      intro β hβ m d
      let d₁ : Fin m → B₁ := fun i => (d i).1
      let d₂ : Fin m → B₂ := fun i => (d i).2
      obtain ⟨c₁, hc₁⟩ := (positive_comparison α hα A₁ B₁ n a₁ b₁).mp h₁ β hβ m d₁
      obtain ⟨c₂, hc₂⟩ := (positive_comparison α hα A₂ B₂ n a₂ b₂).mp h₂ β hβ m d₂
      refine ⟨fun i => (c₁ i, c₂ i), ?_⟩
      have hh := ih β hβ B₁ B₂ A₁ A₂ (n + m)
        (append b₁ d₁) (append b₂ d₂) (append a₁ c₁) (append a₂ c₂) hc₁ hc₂
      rw [append_pair, append_pair] at hh
      simpa only [d₁, d₂] using hh

end LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth
