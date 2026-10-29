module
public import LogicLineages.OrdinalComparison.ControlDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section

/-! Independent encoded-computability component of the source control lemma.
The target uses Mathlib's actual primitive-recursive function predicate;
executability of a Lean definition is not substituted for this statement. -/

namespace LogicLineages.OrdinalComparison.Targets

def FixedControlPrimitiveRecursive : Prop :=
  (∀ j : Nat, Primrec (fastControl j)) ∧ Primrec Phi

end LogicLineages.OrdinalComparison.Targets
