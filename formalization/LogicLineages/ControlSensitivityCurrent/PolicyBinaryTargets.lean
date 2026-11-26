module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceBinaryPlanTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyBinaryTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering ExistentialPlan SourceAdditionCompletion
/-- Actual source-DAG renaming in arbitrary p/f continuations, including equations. -/
def Rename : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ Δ : List Ty) (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat)
  (ν : Variable Δ .ground → Nat), (∀ x, ν (r x)=ρ x) → ∀ q : Plan Γ,
  PolicyPlan.Eval p f ν (BinaryPlan.renamePlan r q) ↔ PolicyPlan.Eval p f ρ q
/-- Literal shared binary DAG run plus the actual one-copy continuation. -/
def Binary : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : Variable Γ .ground → Nat) (b : BinaryDAG) (out : Port Γ) (q : Plan Γ),
  PolicyPlan.Eval p f ρ (BinaryPlan.binaryPlan b out q) ↔
    b.Run (out.value (inputs ρ)) ∧ PolicyPlan.Eval p f ρ q
/-- Every literal, including zero, binds its true natural value in the continuation. -/
def Literal : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : Variable Γ .ground → Nat) (k : Nat) (q : Plan (.ground::Γ)),
  PolicyPlan.Eval p f ρ (BinaryPlan.constantPlan k q) ↔
    PolicyPlan.Eval p f (ExistentialPlan.extend ρ k) q
/-- Exact syntax-only counts, all primitive-lowering witnesses included. -/
def ActualCounts : Prop := BinaryPlan.Targets.RenameSize ∧ BinaryPlan.Targets.BinarySize ∧ BinaryPlan.Targets.LiteralSize
end LogicLineages.ControlSensitivityCurrent.PolicyBinaryTargets
