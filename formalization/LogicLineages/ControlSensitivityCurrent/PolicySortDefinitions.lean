module
public import LogicLineages.ControlSensitivityCurrent.PolicyAdditionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicySort
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion
/-- Actual zero-history assignment at the given policy, same positive raw valuation. -/
def Observation (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground) (y : Nat) : Prop :=
  ∃ v : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment p t = some v ∧
    ParametricSourceSuccessor.denoteWith f (fun c => ((ρ c + 1 : Nat) : Ordinal)) (v 0) =
      ((y + 1 : Nat) : Ordinal)
/-- Four real S graph calls under one joint valuation, with existential outputs. -/
def SortFormula (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : OrdinalComponent Γ → Nat) (a b low high : Variable Γ .ground)
    (difference : Nat) : Prop :=
  ∃ qa qb qlow qhigh : Nat,
    Observation p f ρ (successorProbe a) qa ∧
    Observation p f ρ (successorProbe b) qb ∧
    Observation p f ρ (successorProbe low) qlow ∧
    Observation p f ρ (successorProbe high) qhigh ∧
    qa + qb = qlow + qhigh ∧ input ρ low + difference = input ρ high
end LogicLineages.ControlSensitivityCurrent.PolicySort
