module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem term_renaming_evaluation : Targets.groupTermRenamingEvaluation.{u} := by
  intro G _ n n' ρ t a
  induction t with
  | var i => rfl
  | zero => rfl
  | neg t ih => exact congrArg Neg.neg ih
  | add s t ihs iht => exact congrArg₂ HAdd.hAdd ihs iht

theorem qf_renaming_realization : Targets.groupQFRenamingRealization.{u} := by
  intro G _ n n' ρ q a
  induction q with
  | equal s t =>
    simp only [renameQF, QF.Realize, term_renaming_evaluation G n n' ρ]
  | falsum => exact Iff.rfl
  | neg q ih => exact not_congr ih
  | and q r ihq ihr => exact and_congr ihq ihr

theorem lift_renaming_assignment : Targets.groupLiftRenamingAssignment.{u} := by
  intro G n n' m ρ a d
  funext i
  induction i using Fin.addCases <;> simp [liftRenaming, append]

private theorem realization_aux (G : Type u) [AddCommGroup G] {n : ℕ} (φ : Formula n) :
    ∀ (n' : ℕ) (ρ : Fin n → Fin n') (a : Fin n' → G),
      (renameFormula ρ φ).Realize a ↔ φ.Realize (fun i => a (ρ i)) := by
  induction φ with
  | qf q =>
    intro n' ρ a
    exact qf_renaming_realization G _ n' ρ q a
  | disjEx s m matrix ih =>
    intro n' ρ a
    simp only [renameFormula, Formula.Realize, ih, lift_renaming_assignment G]
  | conjAll s m matrix ih =>
    intro n' ρ a
    simp only [renameFormula, Formula.Realize, ih, lift_renaming_assignment G]

theorem infinitary_renaming_realization : Targets.groupInfinitaryRenamingRealization.{u} := by
  intro G _ n n' ρ φ a
  exact realization_aux G φ n' ρ a

private theorem complexity_aux {side : Polarity} {α : Ordinal.{v}} {n : ℕ} {φ : Formula n}
    (h : Complexity side α φ) :
    ∀ (n' : ℕ) (ρ : Fin n → Fin n'), Complexity side α (renameFormula ρ φ) := by
  induction h with
  | qf side q =>
    intro n' ρ
    exact Complexity.qf side (renameQF ρ q)
  | sigma positive s m matrix β lower rank ih =>
    intro n' ρ
    exact Complexity.sigma positive s m
      (fun i => renameFormula (liftRenaming ρ (m i)) (matrix i)) β lower
      (fun i => ih i (n' + m i) (liftRenaming ρ (m i)))
  | pi positive s m matrix β lower rank ih =>
    intro n' ρ
    exact Complexity.pi positive s m
      (fun i => renameFormula (liftRenaming ρ (m i)) (matrix i)) β lower
      (fun i => ih i (n' + m i) (liftRenaming ρ (m i)))

theorem infinitary_renaming_complexity : Targets.groupInfinitaryRenamingComplexity.{v} := by
  intro side α n n' ρ φ h
  exact complexity_aux h n' ρ

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
