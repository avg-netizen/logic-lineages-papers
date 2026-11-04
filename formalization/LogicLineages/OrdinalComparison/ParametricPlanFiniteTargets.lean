module
public import LogicLineages.OrdinalComparison.ParametricPlanFiniteDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.Targets
open ExistentialPlan PrimitiveLowering ParametricPrimitiveFinite

def GeneratedLeaves : Prop := ∀ (G : Nat → Nat), StrictMono G →
  (∀ n : Nat,n ≤ G n) → ∀ (Γ : List Ty) (g : Gate Γ)
    (ρ : Variable (Block Γ) .ground → Nat), ForestFinite G ρ (forest g)

def UniformCompiler : Prop := ∀ (G : Nat → Nat), StrictMono G →
  (∀ n : Nat,n ≤ G n) → ∀ (Γ : List Ty) (q : Plan Γ), UniformFinite G q →
  ∀ ρ : Variable (compile q).context .ground → Nat,
    ForestFinite G ρ (compile q).forest

def ActualGammaCompiler : Prop := ∀ (b : Nat) (Γ : List Ty) (q : Plan Γ),
  UniformFinite (SourceMachineControlNonperiodicity.gamma b) q →
  ∀ ρ : Variable (compile q).context .ground → Nat,
    SourceGammaAggregate.FiniteLeaves b (positive (inputs ρ))
      ((compile q).forest.map (fun e => (e.1.term,e.2.term)))
end LogicLineages.OrdinalComparison.Source.ParametricPlanFinite.Targets
