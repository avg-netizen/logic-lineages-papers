module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringDefinitions
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan
open ExistentialPlan

def Supported : {Γ : List Ty} → Plan Γ → Prop
  | _, .done => True
  | _, .equation _ _ q => Supported q
  | _, .gate g q => ParametricPrimitiveLowering.Supported g ∧ Supported q
  | _, .existsGround q => Supported q

noncomputable def EvalWith (G : Nat → Nat) {Γ} (ρ : Variable Γ .ground → Nat) : Plan Γ → Prop
  | .done => True
  | .equation a b q => ParametricSourceAddition.Equation G (inputs ρ) a.term b.term ∧ EvalWith G ρ q
  | .gate g q => g.Holds (inputs ρ) ∧ EvalWith G ρ q
  | .existsGround q => ∃ n, EvalWith G (extend ρ n) q

def HoldsWith (G : Nat → Nat) {Γ} (r : Result Γ) (ρ : Variable r.context .ground → Nat) : Prop :=
  ∀ e ∈ r.forest, ParametricSourceAddition.Equation G (inputs ρ) e.1.term e.2.term
end LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan
