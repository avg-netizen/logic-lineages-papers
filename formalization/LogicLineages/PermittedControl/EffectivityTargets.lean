module
public import LogicLineages.PermittedControl.Definitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets

/-- Primitive recursion for the actual lcm/correction/control definitions,
including uniformity in the prescribed prefix parameter. -/
def NearControlPrimitiveRecursive : Prop :=
  Primrec initialLcm ∧ Primrec correction ∧ Primrec₂ nearControl

end LogicLineages.PermittedControl.Targets
