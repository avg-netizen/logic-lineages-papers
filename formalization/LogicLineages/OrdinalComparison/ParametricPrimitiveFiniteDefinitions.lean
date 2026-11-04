module
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite
open PrimitiveLowering

/-- Numerical observation, before the positive raw-ordinal successor. -/
def value (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat) : Expr Γ → Nat
  | .port a => a.value ρ
  | .successor a => G (a.value ρ+4)
  | .erase a b => G (3*a.value ρ+b.value ρ+8)
  | .identityZero => G 6

/-- Every component is interpreted as a strictly positive finite ordinal. -/
def positive {Γ} (ρ : OrdinalComponent Γ → Nat) : OrdinalComponent Γ → Ordinal :=
  fun c => ((ρ c+1 : Nat) : Ordinal)
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite
