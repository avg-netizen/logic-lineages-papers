module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphIndexProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
open LogicLineages.OrdinalComparison.Source
open RawSourceDAG

private theorem tagMod (n t : Nat) (ht : t<8) : (8*n+t)%8=t := by omega
private theorem tagDiv (n t : Nat) (ht : t<8) : (8*n+t)/8=n := by omega

@[simp] theorem literalPayload (d : Code) : payload (Encodable.encode d)=d := by
  simp [payload,Encodable.encodek]

/-- Actual matrix coding commutes with the existing typed source/DAG rename. -/
theorem termRename {Γ Ξ} (r : Renaming Γ Ξ) (a : SourceAST.Term Γ) :
    renameTerm (Ξ.map SyntaxCode.typeCode) (Operations.renamingCode r) (term a) =
      term (CurrentUnitElimination.renameTerm r a) := by
  induction a with
  | var x =>
    rw [term,renameTerm]
    simp only [var,show 8*variableIndex x%8=0 from tagMod _ 0 (by decide),
      show 8*variableIndex x/8=variableIndex x from tagDiv _ 0 (by decide),↓reduceIte,
      CurrentUnitElimination.renameTerm,term,Operations.renaming_lookup]
  | literal n =>
    rw [term,renameTerm]
    simp only [lit,tagMod _ 1 (by decide),tagDiv _ 1 (by decide),reduceCtorEq,
      false_or,↓reduceIte,CurrentUnitElimination.renameTerm,term]
  | add a b ha hb =>
    rw [term,renameTerm]
    simp only [add,tagMod _ 2 (by decide),tagDiv _ 2 (by decide),Nat.unpair_pair,
      reduceCtorEq,true_or,↓reduceIte,CurrentUnitElimination.renameTerm,term] at *
    rw [← ha,← hb]
  | unary h a ih =>
    rw [term,renameTerm]
    simp only [unary,tagMod _ 4 (by decide),tagDiv _ 4 (by decide),Nat.unpair_pair,
      reduceCtorEq,false_or,↓reduceIte,literalPayload,CurrentUnitElimination.renameTerm,term]
    rw [ih]
  | observation d =>
    rw [term,renameTerm]
    simp only [observe,tagMod _ 3 (by decide),tagDiv _ 3 (by decide),reduceCtorEq,
      or_self,↓reduceIte,literalPayload,CurrentUnitElimination.renameTerm,term,
      Operations.rename_input]

theorem formulaRename {Γ Ξ} (r : Renaming Γ Ξ) (a : SourceAST.Formula Γ) :
    renameFormula (Ξ.map SyntaxCode.typeCode) (Operations.renamingCode r) (formula a) =
      formula (CurrentUnitElimination.renameFormula r a) := by
  induction a with
  | truth | falsity => rfl
  | eq a b | le a b | lt a b =>
    rw [formula,renameFormula]
    simp only [eq,le,lt,atom,tagMod _ 2 (by decide),tagMod _ 3 (by decide),tagMod _ 4 (by decide),
      tagDiv _ 2 (by decide),tagDiv _ 3 (by decide),tagDiv _ 4 (by decide),Nat.unpair_pair,
      Nat.reduceLeDiff,↓reduceIte,termRename,CurrentUnitElimination.renameFormula,formula]
  | neg a ih =>
    rw [formula,renameFormula]
    simp only [neg,tagMod _ 5 (by decide),tagDiv _ 5 (by decide),le_refl,↓reduceIte,
      ih,CurrentUnitElimination.renameFormula,formula]
  | conj a b ha hb | disj a b ha hb =>
    rw [formula,renameFormula]
    simp only [both,either,atom,tagMod _ 6 (by decide),tagMod _ 7 (by decide),
      tagDiv _ 6 (by decide),tagDiv _ 7 (by decide),Nat.unpair_pair,Nat.reduceLeDiff,
      reduceCtorEq,↓reduceIte,ha,hb,CurrentUnitElimination.renameFormula,formula]

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
