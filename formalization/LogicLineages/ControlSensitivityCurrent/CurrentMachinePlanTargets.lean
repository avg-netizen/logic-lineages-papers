module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanTargets
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanTargets
public import LogicLineages.ControlSensitivityCurrent.ActualMachineTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentMachinePlanTargets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan PrimitiveLowering

/-- All explicit source equations in this plan are the actual successor observations. -/
def SuccessorEquations {Γ : List Ty} : Plan Γ → Prop
  | .done => True
  | .equation a b q =>
    (∃ x y : Variable Γ .ground, a.term = successorProbe x ∧ b.term = .var y) ∧
      SuccessorEquations q
  | .gate _ q => SuccessorEquations q
  | .existsGround q => SuccessorEquations q

def OriginalPlan : Prop := ∀ b e, SuccessorEquations (SourceMachineConjunctionPlan.plan b e)

def PointwisePlan : Prop :=
  ∀ (b e : Nat) (p : AdmissibleSum.Policy)
    (ρ : Variable SourceMachineConjunctionPlan.Base .ground → Nat),
    PolicyPlan.Eval p (SourceMachineControlNonperiodicity.gamma b) ρ (SourceMachineConjunctionPlan.plan b e) ↔
      SourceMachineHaltingConjunction.Conjunction b e
        (ρ (SourceMachineConjunctionPlan.original 0)) (ρ (SourceMachineConjunctionPlan.original 1))
        (ρ (SourceMachineConjunctionPlan.original 2)) (ρ (SourceMachineConjunctionPlan.original 3))

def CompiledHalting : Prop := ∀ (b e : Nat) (p : AdmissibleSum.Policy),
  (∃ ρ, PolicyPlan.ResultHolds p (SourceMachineControlNonperiodicity.gamma b)
    (compile (SourceMachineConjunctionPlan.plan b e)) ρ) ↔ SourceBlankMachineSimulation.Halts e

end LogicLineages.ControlSensitivityCurrent.CurrentMachinePlanTargets
