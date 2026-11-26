module
public import LogicLineages.ControlSensitivityCurrent.PolicyLoweringDefinitions
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyPlan
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan
/-- Same literal typed Plan, actual p/f source equations under a shared ground valuation. -/
def Eval (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : Variable Γ .ground → Nat) : Plan Γ → Prop
  | .done => True
  | .equation a b q => PolicyAddition.Equation p f (inputs ρ) a.term b.term ∧ Eval p f ρ q
  | .gate g q => g.Holds (inputs ρ) ∧ Eval p f ρ q
  | .existsGround q => ∃ n, Eval p f (extend ρ n) q

def ResultHolds (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ} (r : Result Γ)
    (ρ : Variable r.context .ground → Nat) : Prop :=
  ∀ e ∈ r.forest, PolicyAddition.Equation p f (inputs ρ) e.1.term e.2.term
end LogicLineages.ControlSensitivityCurrent.PolicyPlan
