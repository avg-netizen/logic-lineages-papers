module
public import LogicLineages.ControlSensitivityCurrent.InputNormalizationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.InputNormalizationTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open InputNormalization
/-- Actual typed renaming preserves every Boolean wire, not merely the root. -/
def ReferenceNaturality : Prop := ∀ (Γ Δ : List Ty) (r : Renaming Γ Δ)
  (ρ : Variable Γ .ground → Nat) (σ : Variable Δ .ground → Nat),
  (∀ x, σ (r x) = ρ x) → ∀ (m : Nat) (d : Dag Γ m),
  (d.rename r).eval σ = d.eval ρ
/-- The explicit linear reference-table expansion preserves every Boolean wire. -/
def WireCorrect : Prop := ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
  (m : Nat) (d : Dag Γ m),
  BooleanWire.evaluate d.wires
    (fun i => (d.ports i).value (ExistentialPlan.inputs ρ)) = d.eval ρ
/-- Genuine interleaved input to A-normal Program, all policies and controls.
Both sides interpret actual supplied sources with exactly rawScalar-1. -/
def Normalization : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : Variable Γ .ground → Nat) (m : Nat)
  (d : Dag Γ m) (q : Input Γ m),
  programEval p f ρ (normalize d q) ↔ q.eval p f ρ (d.eval ρ)
/-- Actual output Program budgets, including binary literals and full supplied
source tables. No assertion about encoded bit complexity or AST coverage. -/
def Budgets : Prop := ∀ (Γ : List Ty) (m : Nat) (d : Dag Γ m) (q : Input Γ m),
  (normalize d q).codeSize = q.cost + 3*m ∧
  (normalize d q).sourceMax = q.sourceMax ∧
  (normalize d q).load ≤ (q.cost+3*m)*(q.sourceMax+1)
end LogicLineages.ControlSensitivityCurrent.InputNormalizationTargets
