module
public import LogicLineages.ControlSensitivityCurrent.CompositeEraserDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.GenericScalarTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ParametricSourceSuccessor
/-- Actual evaluation, arbitrary f; no algorithmic claim about f. -/
def BelowEpsilon : Prop := ∀ (f : Nat → Nat) (Γ : List Ty)
  (ρ : OrdinalComponent Γ → Nat) (t : OrdinalExpression Γ),
  denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) t < epsilonZero

def GeneratedPositiveFinite : Prop := ∀ (f : Nat → Nat) (Γ : List Ty)
  (ρ : OrdinalComponent Γ → Nat) (i : Nat) (t : OrdinalExpression Γ),
  GeneratedOrdinalGrade Γ i t →
  0 < denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) t ∧
  (i = 0 → ∃ n : Nat, denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) t = (n : Ordinal))

/-- Real assignment exists, rather than being an input oracle. Positive finite raw inputs
at every coordinate include the full ground-free source domain and any internal type. -/
def ActualSourceTotality : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground),
  ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment p t = some v ∧
    ∃ n : Nat, 0 < n ∧
      denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal) ∧
      ∀ m : Nat, CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) t m ↔ m = n
end LogicLineages.ControlSensitivityCurrent.GenericScalarTargets
