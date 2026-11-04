module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFiniteDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.Targets
open ExistentialPlan BinaryPlan PrimitiveLowering ParametricPlanFinite ParametricScalingPlan

def ForwardRenaming : Prop := ∀ (G : Nat → Nat) (Γ Δ : List Ty)
    (r : Renaming Γ Δ) (q : Plan Γ), UniformFinite G q → UniformFinite G (renamePlan r q)

def ConstructorPreservation : Prop :=
  (∀ (G : Nat → Nat) (Γ : List Ty) (d : SourceAdditionCompletion.BinaryDAG)
    (out : Port Γ) (q : Plan Γ), UniformFinite G q → UniformFinite G (binaryPlan d out q)) ∧
  (∀ (G : Nat → Nat) (Γ : List Ty) (k : Nat) (q : Plan (.ground::Γ)),
    UniformFinite G q → UniformFinite G (constantPlan k q)) ∧
  (∀ (G : Nat → Nat) (Γ : List Ty) (e : Nat) (a out : Port Γ) (q : Plan Γ),
    UniformFinite G q → UniformFinite G (scalePlan e a out q))

def ActualPlanUniformity : Prop := ∀ (G : Nat → Nat), StrictMono G →
  (∀ n : Nat,n ≤ G n) → ∀ b e : Nat,
    UniformFinite G (SourceMachineConjunctionPlan.plan b e)

def ActualGammaForest : Prop := ∀ b e : Nat,
  ∀ ρ : Variable (compile (SourceMachineConjunctionPlan.plan b e)).context .ground → Nat,
    SourceGammaAggregate.FiniteLeaves b (ParametricPrimitiveFinite.positive (inputs ρ))
      ((compile (SourceMachineConjunctionPlan.plan b e)).forest.map (fun f => (f.1.term,f.2.term)))
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.Targets
