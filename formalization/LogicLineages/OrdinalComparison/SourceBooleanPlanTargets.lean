module
public import LogicLineages.OrdinalComparison.SourceBooleanPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanPlan.Targets
open PrimitiveLowering ExistentialPlan

def GatesExact : Prop := ∀ (Γ : List Ty) (gs : List (Gate Γ)) (ρ : Variable Γ .ground → Nat),
  Eval ρ (gates gs) ↔ ∀ g ∈ gs, g.Holds (inputs ρ)

def BindExact : Prop := ∀ (Γ : List Ty) (n : Nat)
    (q : Plan (List.replicate n Ty.ground++Γ)) (ρ : Variable Γ .ground → Nat),
  Eval ρ (bindBlock n q) ↔ ∃ v : Fin n → Nat, Eval (block ρ n v) q

def MatrixExact : Prop := ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m)
    (a : Fin n → Port Γ) (root : Fin m) (ρ : Variable Γ .ground → Nat),
  Eval ρ (matrixPlan d a root) ↔
    BooleanWire.evaluate d (fun i => (a i).value (inputs ρ)) root = true

/-- Exact declared Plan budgets and their linear bounds. The accepted Plan
compiler separately turns these into actual primitive forest bounds. -/
def LinearOverhead : Prop := ∀ (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m)
    (a : Fin n → Port Γ) (root : Fin m),
  (matrixPlan d a root).vertices = 80*(BooleanWire.atomCount d+2) ∧
  (matrixPlan d a root).equations = 10*(BooleanWire.atomCount d+2) ∧
  (matrixPlan d a root).witnesses = (9*m+1)+9*(BooleanWire.atomCount d+2) ∧
  (matrixPlan d a root).vertices ≤ 80*(9*m+2) ∧
  (matrixPlan d a root).equations ≤ 10*(9*m+2) ∧
  (matrixPlan d a root).witnesses ≤ (9*m+1)+9*(9*m+2)
end LogicLineages.OrdinalComparison.Source.BooleanPlan.Targets
