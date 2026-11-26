module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceBooleanPlanTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyMatrixTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering ExistentialPlan
/-- Real finite list of primitive gates, same p/f and one shared ground valuation. -/
def Gates : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty)
  (gs : List (Gate Γ)) (ρ : Variable Γ .ground → Nat),
  PolicyPlan.Eval p f ρ (BooleanPlan.gates gs) ↔ ∀ g ∈ gs, g.Holds (inputs ρ)
/-- Actual finite fresh prefix with every original coordinate preserved by block. -/
def Bind : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (n : Nat)
  (q : Plan (List.replicate n Ty.ground++Γ)) (ρ : Variable Γ .ground → Nat),
  PolicyPlan.Eval p f ρ (BooleanPlan.bindBlock n q) ↔
    ∃ v : Fin n → Nat, PolicyPlan.Eval p f (BooleanPlan.block ρ n v) q
/-- Actual BooleanWire DAG/global flattened gates/typed Plan, not a supplied oracle. -/
def Matrix : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (n m : Nat) (d : BooleanWire.Dag n m) (a : Fin n → Port Γ)
  (root : Fin m) (ρ : Variable Γ .ground → Nat),
  PolicyPlan.Eval p f ρ (BooleanPlan.matrixPlan d a root) ↔
    BooleanWire.evaluate d (fun i => (a i).value (inputs ρ)) root=true
/-- Literal Plan vertex/equation/witness counts, not global output DAG complexity. -/
def ActualSize : Prop := BooleanPlan.Targets.LinearOverhead
end LogicLineages.ControlSensitivityCurrent.PolicyMatrixTargets
