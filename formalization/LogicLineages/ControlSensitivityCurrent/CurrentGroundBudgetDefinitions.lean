module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open OriginalSecondBudget

/-- First field paired with the original whole-box second field. -/
def boxFirst (k : Nat) : Fin ((Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level+1) :=
  ⟨1,by have h := (boxSecond k).isLt; change 2 < _ at h; omega⟩

/-- Literal original selected-policy scalar, never the scalar of the new
unary source. The second-count fold itself is policy independent. -/
def budgetCode (p : AdmissibleSum.Policy) (Γ : List Nat) (body : Nat) : Option Nat :=
  (PolicyAssignment.assignmentCode p Γ body).map
    (fun u => OriginalBudgetCode.secondCode (u.getD 0 0))

end LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget
