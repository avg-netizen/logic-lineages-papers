module
public import LogicLineages.ControlSensitivityCurrent.CompositeEraserDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyCollision
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
/-- Literal control-shifted coefficient-one collapse value. -/
def g (f : Nat → Nat) (n : Nat) : Nat := f (n+2)+1
def leftValue (f : Nat → Nat) (x y : Nat) : Nat :=
  g f (3*g f (3*x+x+2) + g f (3*y+y+2)+2)
def rightValue (f : Nat → Nat) (x y : Nat) : Nat :=
  g f (3*g f (3*x+y+2) + g f (3*y+x+2)+2)
/-- Actual canonical scalar; source totality must eliminate the zero fallback. -/
noncomputable def rawScalar (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground) : Nat :=
  ((AdmissibleAssignment.assignment p t).map (fun v => OriginalDomain.finiteValue
    (ParametricSourceSuccessor.denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0)))).getD 0
end LogicLineages.ControlSensitivityCurrent.PolicyCollision
