module
public import LogicLineages.ControlSensitivityCurrent.PolicySortDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CompositeEraser
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
/-- Genuine arbitrary-policy canonical assignment and selected-control finite denotation. -/
def Scalar (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ν : OrdinalComponent Γ → Ordinal) (t : OriginalTerm Γ .ground) (n : Nat) : Prop :=
  ∃ v : OrdinalVector Γ 0, AdmissibleAssignment.assignment p t = some v ∧
    ParametricSourceSuccessor.denoteWith f ν (v 0) = (n : Ordinal)
end LogicLineages.ControlSensitivityCurrent.CompositeEraser
