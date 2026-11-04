module
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Targets
open SourceAdditionCompletion PrimitiveLowering ExistentialPlan BinaryPlan ParametricExistentialPlan

def ExactRenaming : Prop :=
  (∀ (G : Nat → Nat) (Γ Δ : List Ty) (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
    (∀ x,ν (r x)=ρ x) → ∀ q : Plan Γ, EvalWith G ν (renamePlan r q) ↔ EvalWith G ρ q) ∧
  (∀ (Γ Δ : List Ty) (r : Renaming Γ Δ) (q : Plan Γ), Supported (renamePlan r q) ↔ Supported q)

def ExactBinaryPlan : Prop :=
  (∀ (G : Nat → Nat) (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (b : BinaryDAG) (out : Port Γ) (q : Plan Γ),
    EvalWith G ρ (binaryPlan b out q) ↔ out.value (inputs ρ)=value b ∧ EvalWith G ρ q) ∧
  (∀ (Γ : List Ty) (b : BinaryDAG) (out : Port Γ) (q : Plan Γ),
    Supported (binaryPlan b out q) ↔ Supported q) ∧
  (∀ k : Nat,value (binaryDAG k)=k)

def ActualGammaLiteralCompilation : Prop := ∀ (b k : Nat) (Γ : List Ty)
    (q : Plan (.ground::Γ)), Supported q → ∀ ρ : Variable Γ .ground → Nat,
    (∃ ν : Variable (compile (constantPlan k q)).context .ground → Nat,
      (∀ x,ν ((compile (constantPlan k q)).embedding x)=ρ x) ∧
      HoldsWith (SourceMachineControlNonperiodicity.gamma b) (compile (constantPlan k q)) ν) ↔
    EvalWith (SourceMachineControlNonperiodicity.gamma b) (ExistentialPlan.extend ρ k) q

def ExactCompiledBounds : Prop := ∀ (Γ : List Ty) (k : Nat) (q : Plan (.ground::Γ)),
  (compile (constantPlan k q)).nodes ≤ 80*(4*(Nat.log2 k+1)+1)+q.vertices ∧
  (compile (constantPlan k q)).forest.length ≤ 10*(4*(Nat.log2 k+1)+1)+q.equations ∧
  (compile (constantPlan k q)).context.length ≤ Γ.length+40*(Nat.log2 k+1)+10+q.witnesses
end LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Targets
