module
public import LogicLineages.OrdinalComparison.WWSelectedBinderTargets
public import LogicLineages.OrdinalComparison.WWSourceRenamingStatementChecks
public import LogicLineages.OrdinalComparison.SourceStructural
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinder.Proof
open SourceTypedPorts

theorem swap_swap {Γ : List Ty} {σ τ υ : Ty} (x : Variable (σ :: τ :: Γ) υ) :
    swap (swap x) = x := by
  cases x with
  | here => rfl
  | there x => cases x <;> rfl

theorem lift_inverse {Γ Δ : List Ty} {σ τ : Ty} (f : Renaming Γ Δ) (g : Renaming Δ Γ)
    (h : ∀ {υ} (x : Variable Γ υ), g (f x) = x) (x : Variable (σ :: Γ) τ) :
    Renaming.lift g (Renaming.lift f x) = x := by
  cases x with
  | here => rfl
  | there x => exact congrArg Variable.there (h x)

theorem from_to (left right : List Ty) (σ τ : Ty)
    (x : Variable (left ++ σ :: right) τ) :
    moveFromHead left right σ (moveToHead left right σ x) = x := by
  cases left with
  | nil => rfl
  | cons a left =>
      simp only [moveToHead,moveFromHead,swap_swap]
      exact lift_inverse _ _ (fun {υ} x => from_to left right σ υ x) x
termination_by left.length

theorem to_from (left right : List Ty) (σ τ : Ty)
    (x : Variable (σ :: (left ++ right)) τ) :
    moveToHead left right σ (moveFromHead left right σ x) = x := by
  cases left with
  | nil => rfl
  | cons a left =>
      simp only [moveToHead,moveFromHead]
      rw [lift_inverse _ _ (fun {υ} x => to_from left right σ υ x),swap_swap]
termination_by left.length

theorem inverses : Targets.Inverses := by
  intro left right σ τ
  exact ⟨from_to left right σ τ,to_from left right σ τ⟩

theorem indices : Targets.Indices := by
  intro left right σ τ x
  induction left with
  | nil =>
      cases x with
      | here => rfl
      | there x => simp [moveToHead,variableIndex]
  | cons a left ih =>
      cases x with
      | here => simp [moveToHead,Renaming.lift,swap,variableIndex]
      | there x =>
          have hx := ih x
          cases he : moveToHead left right σ x with
          | here =>
              simp only [he,variableIndex] at hx
              simp only [moveToHead,Renaming.lift,he,swap,variableIndex,List.length_cons]
              split_ifs at hx ⊢ <;> omega
          | there y =>
              simp only [he,variableIndex] at hx
              simp only [moveToHead,Renaming.lift,he,swap,variableIndex,List.length_cons]
              split_ifs at hx ⊢ <;> omega

theorem to_selected (left right : List Ty) (σ : Ty) :
    moveToHead left right σ (SelectedBinder.selected left right σ) = .here := by
  induction left with
  | nil => rfl
  | cons a left ih => simp [SelectedBinder.selected,moveToHead,Renaming.lift,ih,swap]

theorem selected : Targets.Selected := by
  intro left right σ
  refine ⟨to_selected left right σ, ?_⟩
  have h := from_to left right σ σ (SelectedBinder.selected left right σ)
  rw [to_selected] at h
  exact h

theorem sourceRoundTrip : Targets.SourceRoundTrip := by
  intro left right σ τ t
  rw [Term.rename_composition]
  have h : (fun {υ} (x : Variable (left ++ σ :: right) υ) =>
      moveFromHead left right σ (moveToHead left right σ x)) = (fun {_} x => x) := by
    funext υ x
    exact from_to left right σ υ x
  rw [h,Term.rename_identity]

theorem assignmentNaturality : Targets.AssignmentNaturality := by
  intro left right σ τ p t
  exact SourceRenaming.StatementChecks.assignmentNaturality _ _ _ (moveToHead left right σ) p t

theorem valuationNaturality : Targets.ValuationNaturality := by
  intro left right σ ρ
  constructor
  · rintro ⟨τ,x,j⟩
    simp only [transport,ordinalComponentRename,from_to]
  · intro j
    simp only [transport,ordinalComponentRename,(selected left right σ).2]
end LogicLineages.OrdinalComparison.Source.SelectedBinder.Proof
