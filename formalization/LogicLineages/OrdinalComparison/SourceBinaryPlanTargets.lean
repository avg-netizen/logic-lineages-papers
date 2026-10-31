module
public import LogicLineages.OrdinalComparison.SourceBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BinaryPlan.Targets
open PrimitiveLowering ExistentialPlan SourceAdditionCompletion

def RenameCorrect : Prop := ∀ (Γ Δ : List Ty) (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
  (∀ x, ν (r x)=ρ x) → (∀ q : Plan Γ, (Eval ν (renamePlan r q) ↔ Eval ρ q))

def RenameSize : Prop := ∀ (Γ Δ : List Ty) (r : Renaming Γ Δ) (q : Plan Γ),
  (renamePlan r q).vertices=q.vertices ∧ (renamePlan r q).equations=q.equations ∧
    (renamePlan r q).witnesses=q.witnesses

def BinaryCorrect : Prop := ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (b : BinaryDAG) (out : Port Γ) (q : Plan Γ),
  Eval ρ (binaryPlan b out q) ↔ b.Run (out.value (inputs ρ)) ∧ Eval ρ q

/-- Includes all nine primitive-lowering witnesses per gate, not merely the
explicit existential binders. The single continuation is never multiplied. -/
def BinarySize : Prop := ∀ (Γ : List Ty) (b : BinaryDAG) (out : Port Γ) (q : Plan Γ),
  (binaryPlan b out q).vertices ≤ 80*(2*b.gates+1)+q.vertices ∧
  (binaryPlan b out q).equations ≤ 10*(2*b.gates+1)+q.equations ∧
  (binaryPlan b out q).witnesses ≤ 20*b.gates+9+q.witnesses

def LiteralCorrect : Prop := ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (k : Nat) (q : Plan (.ground::Γ)),
  Eval ρ (constantPlan k q) ↔ Eval (ExistentialPlan.extend ρ k) q

/-- Logarithmic actual-source-plan overhead once lowered by the accepted
existential-plan compiler. No expanded-source-tree/evaluation-time claim. -/
def LiteralSize : Prop := ∀ (Γ : List Ty) (k : Nat) (q : Plan (.ground::Γ)),
  (constantPlan k q).vertices ≤ 80*(4*(Nat.log2 k+1)+1)+q.vertices ∧
  (constantPlan k q).equations ≤ 10*(4*(Nat.log2 k+1)+1)+q.equations ∧
  (constantPlan k q).witnesses ≤ 40*(Nat.log2 k+1)+10+q.witnesses
end LogicLineages.OrdinalComparison.Source.BinaryPlan.Targets
