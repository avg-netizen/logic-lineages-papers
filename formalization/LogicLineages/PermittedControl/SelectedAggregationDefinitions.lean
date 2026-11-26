module
public import LogicLineages.PermittedControl.SelectedFunctionalDetectorDefinitions
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAggregation
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum

/-- Actual successful finite output, ruling out fallback-zero reasoning. -/
def GroundResult {Γ} (ctrl : Nat → Nat) (policy : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ) (t : OriginalTerm Γ .ground) : Prop :=
  ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment policy t=some v ∧
    expressionValue ctrl ρ (v 0)=(groundValue ctrl policy ρ t : Ordinal) ∧
    0<groundValue ctrl policy ρ t

def AllEqual {Γ} (ctrl : Nat → Nat) (policy : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  ∀ e ∈ es, groundValue ctrl policy ρ e.1=groundValue ctrl policy ρ e.2

/-- Literal leaf redetection followed by the existing identically shaped fold. -/
def AggregateAt {Γ} (ctrl : Nat → Nat) (policy : Policy)
    (ρ : AdmissibleSubstitution ctrl Γ)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  let pair := SourceAggregateCompletion.aggregate es
  let l := groundValue ctrl policy ρ pair.1
  let r := groundValue ctrl policy ρ pair.2
  GroundResult ctrl policy ρ pair.1 ∧ GroundResult ctrl policy ρ pair.2 ∧
  r≤l ∧ (l=r ↔ AllEqual ctrl policy ρ es) ∧
  (¬AllEqual ctrl policy ρ es → r+2≤l)
end LogicLineages.PermittedControl.SelectedAggregation
