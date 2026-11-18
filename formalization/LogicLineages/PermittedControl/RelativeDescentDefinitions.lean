module
public import LogicLineages.PermittedControl.RelativeNormDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Relative maximum implemented by actual absolute maximum and ordinary left
subtraction. The greatest-candidate specification is a separate proof. -/
noncomputable def relativeMaximum (mu rho : Ordinal.{0}) (b : Nat) : Ordinal :=
  actualMaximumPredecessor (mu + rho) b - mu

/-- Relative states of the genuine absolute selected-control descent. -/
noncomputable def relativeState (f : Nat → Nat) (lam mu : Ordinal.{0}) (t i : Nat) : Ordinal :=
  (descentWith f)^[i] (countInitial lam t) - mu

end LogicLineages.PermittedControl
