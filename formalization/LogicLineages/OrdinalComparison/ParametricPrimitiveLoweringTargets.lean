module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.Targets
open PrimitiveLowering

def SharedInputsAndSyntax : Prop :=
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (z : Fin 9 → Nat),
    (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
      extend ρ 9 z ⟨τ,shift 9 x,j⟩ = ρ ⟨τ,x,j⟩) ∧
    (∀ i : Fin 9, extend ρ 9 z ⟨.ground,fresh i,0⟩ = z i)) ∧
  (∀ (Γ : List Ty) (e : Expr Γ), e.graph.term = e.term ∧ e.graph.specs.length ≤ 4)

def ExactSupportedLowering : Prop := ∀ G : Nat → Nat,
  StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ), Supported g →
    ∀ z : Fin 9 → Nat,
      (SourceHolds G ρ g z ↔ g.Holds ρ ∧ z = canonicalWitness ρ g) ∧
      (ForestHolds G ρ g z ↔ g.Holds ρ ∧ z = canonicalWitness ρ g)

def ActualGammaLowering : Prop := ∀ b : Nat,
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ), Supported g →
    (∀ z : Fin 9 → Nat,
      ForestHolds (SourceMachineControlNonperiodicity.gamma b) ρ g z ↔
        g.Holds ρ ∧ z = canonicalWitness ρ g) ∧
    ((∃ z : Fin 9 → Nat, ForestHolds (SourceMachineControlNonperiodicity.gamma b) ρ g z) ↔ g.Holds ρ)

def ExactSize : Prop := ∀ (Γ : List Ty) (g : Gate Γ), Supported g →
  (lower g).length = 10 ∧ (forest g).length = 10 ∧ forestNodes g ≤ 80
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveLowering.Targets
