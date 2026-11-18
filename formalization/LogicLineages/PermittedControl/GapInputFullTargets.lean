module
public import LogicLineages.PermittedControl.GapInputTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets

/-- Whole source lem:gap-input, including its explicitly effective threshold
and every actual count/strict-terminal comparison clause. -/
def FullGapInput : Prop := GapInputTailEffective ∧ GapInputComparison

end LogicLineages.PermittedControl.Targets
