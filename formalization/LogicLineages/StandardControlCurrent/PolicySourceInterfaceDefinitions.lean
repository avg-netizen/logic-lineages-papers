module
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityDefinitions
public import LogicLineages.OrdinalComparison.GeneralOmegaHeadLimitTargets
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceInterface
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
/-- Actual literal assignment followed by refusing structural extraction. -/
def compile (p : Policy) (d n : Nat) : Option EncodedVector := do
  let v ← PolicyAssignment.assignmentCode p (List.replicate d 0) n
  compileVectorCode v
end LogicLineages.StandardControlCurrent.PolicySourceInterface
