module
public import LogicLineages.OrdinalComparison.SourceAffinePlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AffinePlan.Targets
open PrimitiveLowering ExistentialPlan

def AddBind : Prop := ∀ Γ (ρ : Variable Γ .ground → Nat) (a b : Port Γ) (q : Plan (.ground::Γ)),
  Eval ρ (addBind a b q) ↔ Eval (extend ρ (a.value (inputs ρ)+b.value (inputs ρ))) q

def Multiply : Prop := ∀ Γ (ρ : Variable Γ .ground → Nat) p (a out : Port Γ) (q : Plan Γ),
  Eval ρ (mulPlan p a out q) ↔ p*a.value (inputs ρ)=out.value (inputs ρ) ∧ Eval ρ q

def MultiplySize : Prop := ∀ Γ p (a out : Port Γ) (q : Plan Γ),
  (mulPlan p a out q).vertices=80*(p+1)+q.vertices ∧
  (mulPlan p a out q).equations=10*(p+1)+q.equations ∧
  (mulPlan p a out q).witnesses=10*p+9+q.witnesses

def MultiplyBind : Prop := ∀ Γ (ρ : Variable Γ .ground → Nat) p (a : Port Γ) (q : Plan (.ground::Γ)),
  Eval ρ (mulBind p a q) ↔ Eval (extend ρ (p*a.value (inputs ρ))) q

def Affine : Prop := ∀ Γ (ρ : Variable Γ .ground → Nat) p c (a x y : Port Γ),
  Eval ρ (affinePlan p c a x y) ↔ p*a.value (inputs ρ)+x.value (inputs ρ)=c+y.value (inputs ρ)
end LogicLineages.OrdinalComparison.Source.AffinePlan.Targets
