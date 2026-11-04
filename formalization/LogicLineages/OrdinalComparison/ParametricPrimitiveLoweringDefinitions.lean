module
public import LogicLineages.OrdinalComparison.ParametricSourceOneDefinitions
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering
open PrimitiveLowering

/-- Exactly the existing eq/add/one syntax; sorting is not transferred. -/
def Supported {Γ} : Gate Γ → Prop
  | .eq _ _ | .add _ _ _ | .one _ => True
  | .sort _ _ _ _ => False

def SourceHolds (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (g : Gate Γ) (z : Fin 9 → Nat) : Prop :=
  ∀ e ∈ lower g, ParametricSourceAddition.Equation G (extend ρ 9 z) e.1.term e.2.term

def ForestHolds (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (g : Gate Γ) (z : Fin 9 → Nat) : Prop :=
  ∀ e ∈ forest g, ParametricSourceAddition.Equation G (extend ρ 9 z) e.1.term e.2.term
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering
