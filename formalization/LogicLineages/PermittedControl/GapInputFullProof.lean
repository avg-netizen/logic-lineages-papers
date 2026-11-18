module
public import LogicLineages.PermittedControl.GapInputFullTargets
public import LogicLineages.PermittedControl.GapInputProof

@[expose] public section
namespace LogicLineages.PermittedControl
 theorem fullGapInput : Targets.FullGapInput := ⟨gapInputTailEffective, gapInputComparison⟩
end LogicLineages.PermittedControl
