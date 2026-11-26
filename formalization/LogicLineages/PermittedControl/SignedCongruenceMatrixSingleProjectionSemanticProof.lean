module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjectionTargets
import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionStatementChecks
import LogicLineages.PermittedControl.SignedCongruenceMatrixLowStripsStatementChecks
import LogicLineages.PermittedControl.SignedRowSingleProjectionCutoffProof

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjection
open HighTailCongruenceMatrixProjection (projected)
open SignedCongruenceMatrix (actualRows commonTail)
open SignedRowSingleProjection (cutoffCaseSplit)
open StatementChecks (fixed_actualSignedCongruenceMatrixLowStrips fixed_actualHighTailCongruenceMatrixProjection)

theorem actualJointCaseSplit : ActualJointCaseSplit := by
  intro f B hf name rank rows ρ ν chosen valid others tied
  let holds : Nat → Prop := fun z =>
    ∃ values : List (List Nat), actualRows f (Function.update ρ rank z) rows values
  have low : (∃ z : Nat, z < commonTail B rows ∧ holds z) ↔ LowHit f ρ B rank rows := by
    simpa only [holds,LowHit,true_and] using fixed_actualSignedCongruenceMatrixLowStrips
      f ρ (fun _ => True) rank (commonTail B rows) rows (fun r member => (valid r member).1)
  have high : (projected B name rows).eval ν ↔ ∃ z : Nat, commonTail B rows ≤ z ∧ holds z :=
    fixed_actualHighTailCongruenceMatrixProjection f B hf name rank rows ρ ν chosen valid others tied
  exact cutoffCaseSplit (commonTail B rows) holds (LowHit f ρ B rank rows) ((projected B name rows).eval ν) low high

end LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjection
