module
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineAggregateBridgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment
open ExistentialPlan SourceGroundBinderFragment

def PlanFragment : {Γ : List Ty} → Plan Γ → Prop
  | _,.done => True
  | _,.equation a b q => Fragment a.term ∧ Fragment b.term ∧ PlanFragment q
  | _,.gate _ q => PlanFragment q
  | _,.existsGround q => PlanFragment q
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment
