module
public import LogicLineages.PermittedControl.EvaluatorDefinitions
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

/-- Source J_lambda(t) initial state; source meaning requires N(lambda)<=t. -/
noncomputable def countInitial (lam : Ordinal.{0}) (t : Nat) : Ordinal :=
  lam + ((t - actualOrdinalNorm lam : Nat) : Ordinal)
noncomputable def completeCount (f : Nat → Nat) (lam : Ordinal.{0}) (t : Nat) : Nat :=
  (terminalWith f (countInitial lam t)).2
noncomputable def completeEndpoint (f : Nat → Nat) (lam : Ordinal.{0}) (t : Nat) : Nat :=
  (terminalWith f (countInitial lam t)).1
noncomputable def headCollapse (f : Nat → Nat) (lam : Ordinal.{0}) (t : Nat) : Nat :=
  collapseWith f (countInitial lam t)

/-- Exact source controls with their corresponding modular-tail threshold. -/
def SelectedWithThreshold (f : Nat → Nat) (B : Nat) : Prop :=
  (f = factorialControl ∧ B = 0) ∨ ∃ b : Nat, f = nearControl b ∧ B = b + 1

end LogicLineages.PermittedControl
