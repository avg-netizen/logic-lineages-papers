module
public import LogicLineages.OrdinalComparison.ParametricScalingPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Targets
open PrimitiveLowering ExistentialPlan ParametricExistentialPlan

def ExactScalingPlan : Prop :=
  (∀ (G : Nat → Nat) (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (e : Nat) (a out : Port Γ) (q : Plan Γ),
    EvalWith G ρ (scalePlan e a out q) ↔
      out.value (inputs ρ)=2^e*a.value (inputs ρ) ∧ EvalWith G ρ q) ∧
  (∀ (Γ : List Ty) (e : Nat) (a out : Port Γ) (q : Plan Γ),
    Supported (scalePlan e a out q) ↔ Supported q)

def ActualGammaScalingCompilation : Prop := ∀ (b e : Nat) (Γ : List Ty)
    (a out : Port Γ) (q : Plan Γ), Supported q → ∀ ρ : Variable Γ .ground → Nat,
    (∃ ν : Variable (compile (scalePlan e a out q)).context .ground → Nat,
      (∀ x,ν ((compile (scalePlan e a out q)).embedding x)=ρ x) ∧
      HoldsWith (SourceMachineControlNonperiodicity.gamma b) (compile (scalePlan e a out q)) ν) ↔
    out.value (inputs ρ)=2^e*a.value (inputs ρ) ∧ EvalWith (SourceMachineControlNonperiodicity.gamma b) ρ q

def ExactOverhead : Prop := ∀ (Γ : List Ty) (e : Nat) (a out : Port Γ) (q : Plan Γ),
  (scalePlan e a out q).vertices=80*(e+1)+q.vertices ∧
  (scalePlan e a out q).equations=10*(e+1)+q.equations ∧
  (scalePlan e a out q).witnesses=10*e+9+q.witnesses ∧
  (compile (scalePlan e a out q)).nodes ≤ 80*(e+1)+q.vertices ∧
  (compile (scalePlan e a out q)).forest.length=10*(e+1)+q.equations ∧
  (compile (scalePlan e a out q)).context.length=Γ.length+10*e+9+q.witnesses
end LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Targets
