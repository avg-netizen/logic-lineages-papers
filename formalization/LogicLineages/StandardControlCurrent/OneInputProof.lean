module
public import LogicLineages.StandardControlCurrent.OneInputTargets
public import LogicLineages.OrdinalComparison.OneInputBooleanProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent

theorem oneInputQuantifiedComparison : OneInputTargets.OneInputQuantifiedComparison :=
  OrdinalComparison.OneInputBoolean.full

end LogicLineages.StandardControlCurrent
