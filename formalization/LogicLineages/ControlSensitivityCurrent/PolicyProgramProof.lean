module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramLowerProof
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgram
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan BooleanCompiler

theorem forest : PolicyProgramTargets.Forest := by
  intro f hf p Γ q
  constructor
  · intro ρ
    exact (lowering p f Γ ρ q).trans (PolicyPlan.compilation f hf p Γ (lower q) ρ)
  · exact (PolicyPlan.actualSize Γ (lower q)).2.2.2
end LogicLineages.ControlSensitivityCurrent.PolicyProgram
