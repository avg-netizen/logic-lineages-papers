module
public import LogicLineages.ControlSensitivityCurrent.SourceASTDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.SourceASTTermTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAST PrimitiveLowering
/-- Genuine CPS semantic preservation with a specified continuation. The later
whole AST compiler must instantiate and prove this continuation specification. -/
def Semantic : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ Δ : List Ty) (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat)
  (ν : Variable Δ .ground → Nat), (∀ x, ν (r x)=ρ x) →
  ∀ (m : Nat) (v : Fin m → Bool) (e : Term Γ) (k : Continuation Δ m) (P : Nat → Prop),
  (∀ (Ξ : List Ty) (s : Renaming Δ Ξ) (μ : Variable Ξ .ground → Nat),
    (∀ x, μ (s x)=ν x) → ∀ a : Port Ξ,
    (k s a).eval p f μ v ↔ P (a.value (ExistentialPlan.inputs μ))) →
  ((e.emit r k).eval p f ν v ↔ P (e.eval p f ρ))
/-- Uniform continuation budget; literal emitted Input.cost, not a semantic size. -/
def Cost : Prop := ∀ (Γ Δ : List Ty) (m : Nat) (r : Renaming Γ Δ)
  (e : Term Γ) (k : Continuation Δ m) (K : Nat),
  (∀ (Ξ : List Ty) (s : Renaming Δ Ξ) (a : Port Ξ), (k s a).cost ≤ K) →
  (e.emit r k).cost ≤ e.cost+K
/-- Actual supplied table lengths survive typed renaming. -/
def SourceTables : Prop := ∀ (Γ Δ : List Ty) (m : Nat) (r : Renaming Γ Δ)
  (e : Term Γ) (k : Continuation Δ m) (M : Nat),
  (∀ (Ξ : List Ty) (s : Renaming Δ Ξ) (a : Port Ξ), (k s a).sourceMax ≤ M) →
  (e.emit r k).sourceMax ≤ max e.sourceMax M
end LogicLineages.ControlSensitivityCurrent.SourceASTTermTargets
