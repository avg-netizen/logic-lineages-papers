module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDriverTargets

public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison Source Source.ForwardTranslation

attribute [local irreducible] StandardControlCurrent.PolicySourceInterface.compile

theorem exactIndexedDecision : ExactIndexedDecision := by
  intro source hsource cbd query rel e p he x
  obtain ⟨d,a,b⟩ := x
  unfold indexedDecision pointwiseDecision
  change (source (e,d,a)).bind _ =
    Part.some (((StandardControlCurrent.PolicySourceInterface.compile p d a).bind _).getD false)
  rw [hsource e p he d a]
  cases ha : StandardControlCurrent.PolicySourceInterface.compile p d a with
  | none => rfl
  | some ea =>
    change (source (e,d,b)).map _ =
      Part.some (((StandardControlCurrent.PolicySourceInterface.compile p d b).map _).getD false)
    rw [hsource e p he d b]
    rfl

#print axioms exactIndexedDecision
end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
