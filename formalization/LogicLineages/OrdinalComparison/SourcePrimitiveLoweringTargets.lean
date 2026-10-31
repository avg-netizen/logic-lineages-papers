module
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Targets
open SourceAdditionCompletion

def SharedInputs : Prop := ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (z : Fin 9 → Nat),
  (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
    extend ρ 9 z ⟨τ,shift 9 x,j⟩ = ρ ⟨τ,x,j⟩) ∧
  (∀ i : Fin 9, extend ρ 9 z ⟨.ground,fresh i,0⟩ = z i)

def SourceExact : Prop := ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (z : Fin 9 → Nat),
  SourceHolds ρ g z ↔ g.Holds ρ ∧ z = canonicalWitness ρ g

def PrimitiveRealization : Prop := ∀ (Γ : List Ty) (e : Expr Γ),
  e.graph.term = e.term ∧ e.graph.specs.length ≤ 4

/-- Genuine actual primitive source-DAG forest, not a count of arithmetic
constraints or an assumed graph of an arbitrary functional oracle. -/
def GraphExact : Prop := ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (z : Fin 9 → Nat),
  (∀ e ∈ forest g, Equation (extend ρ 9 z) e.1.term e.2.term) ↔
    g.Holds ρ ∧ z = canonicalWitness ρ g

def FixedSize : Prop := ∀ (Γ : List Ty) (g : Gate Γ),
  (lower g).length = 10 ∧ (forest g).length = 10 ∧ forestNodes g ≤ 80
end LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Targets
