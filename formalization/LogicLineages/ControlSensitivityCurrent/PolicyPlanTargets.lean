module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanDefinitions
public import LogicLineages.ControlSensitivityCurrent.FullAdditionTargets
public import LogicLineages.OrdinalComparison.SourceExistentialPlanTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyPlanTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan
/-- Actual shared ground valuation bridge, not arbitrary functional ordinal semantics. -/
def EquationNaturality : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ Δ : List Ty) (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat)
  (ν : Variable Δ .ground → Nat), (∀ x, ν (r x) = ρ x) →
  ∀ a b : OriginalTerm Γ .ground,
    PolicyAddition.Equation p f (inputs ν) (a.rename r) (b.rename r) ↔
      PolicyAddition.Equation p f (inputs ρ) a b

def Compilation : Prop := ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (p : AdmissibleSum.Policy) (Γ : List Ty) (q : Plan Γ) (ρ : Variable Γ .ground → Nat),
  PolicyPlan.Eval p f ρ q ↔ ∃ ν : Variable (compile q).context .ground → Nat,
    (∀ x, ν ((compile q).embedding x) = ρ x) ∧ PolicyPlan.ResultHolds p f (compile q) ν
/-- Actual compiled typed forest/context budgets, only Plan-local. -/
def ActualSize : Prop := ExistentialPlan.Targets.Size
end LogicLineages.ControlSensitivityCurrent.PolicyPlanTargets
