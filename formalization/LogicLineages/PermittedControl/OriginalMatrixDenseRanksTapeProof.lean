module
public import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixDenseRanks
open PreparedProjection (LowerOperand lowerOperandRead LowerOperandActual)
open OriginalMatrixActualReadTape (readTape)

theorem exactRenamedOperand (f θ σ rename : Nat → Nat) (op : LowerOperand)
    (tie : σ (rename op.rank) = θ op.rank) :
    (renameOperand rename op).rank = rename op.rank ∧
    lowerOperandRead f σ (renameOperand rename op) = lowerOperandRead f θ op ∧
    ∀ v : Nat, LowerOperandActual f σ (renameOperand rename op) v ↔ LowerOperandActual f θ op v := by
  cases op <;> simp only [LowerOperand.rank] at tie
  all_goals
    refine ⟨rfl,?_,?_⟩
    · simp only [renameOperand,lowerOperandRead,tie]
    · intro v
      simp only [renameOperand,LowerOperandActual,tie]

theorem exactRenamedReadTape : ExactRenamedReadTape := by
  refine ⟨exactRenamedOperand,?_⟩
  intro f θ σ rename terms tied
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      have h := (exactRenamedOperand f θ σ rename t.2 (tied t List.mem_cons_self)).2.1
      have next := ih (fun u hu => tied u (List.mem_cons_of_mem _ hu))
      simp only [List.map_cons,readTape,renameTerm,h,next]
      cases seen : lowerOperandRead f θ t.2 with
      | none => rfl
      | some q =>
          cases q with
          | none => rfl
          | some v =>
              cases more : readTape f θ terms <;> rfl

end LogicLineages.PermittedControl.OriginalMatrixDenseRanks
