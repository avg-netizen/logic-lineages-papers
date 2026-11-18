module
public import LogicLineages.PermittedControl.EvaluatorDefinitions
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison
open OrdinalComparison.ParametricActualCollapse

/-- Actual first-finite endpoint, exact event count, and the source norm orbit. -/
def TerminalSemantics (f : Nat → Nat) : Prop :=
  ∀ (a : Ordinal.{0}), a < epsilonZero →
    (descentWith f)^[ (terminalWith f a).2 ] a = ((terminalWith f a).1 : Ordinal) ∧
    (∀ k : Nat, k < (terminalWith f a).2 → Ordinal.omega0 ≤ (descentWith f)^[k] a) ∧
    collapseWith f a = (terminalWith f a).1 + (terminalWith f a).2 ∧
    (terminalWith f a).1 = f^[ (terminalWith f a).2 ] (actualOrdinalNorm a) ∧
    (Ordinal.omega0 ≤ a → 0 < (terminalWith f a).2 ∧ (terminalWith f a).2 < (terminalWith f a).1)

/-- Numerical program completeness: literal first finite search, not an
unspecified halting witness, with all-natural-input totality and Computable. -/
def EffectiveEvaluation (f : Nat → Nat) : Prop :=
  (∀ (a : NONote), (terminalWith f a.1.repr).2 ∈ terminalSearchWith f (rawNoteEncode a.1) ∧
    encodedFiniteValue (encodedStatesWith f (rawNoteEncode a.1) (terminalWith f a.1.repr).2) =
      (terminalWith f a.1.repr).1) ∧
  Partrec (evaluatorPartialWith f) ∧
  (∀ n : Nat, (evaluatorPartialWith f n).Dom) ∧
  Computable (evaluatorWith f) ∧
  (∀ (a : NONote), evaluatorWith f (rawNoteEncode a.1) = collapseWith f a.1.repr)

/-- Source generic computable-control interface, per function, without a
uniform higher-order control-index claim. -/
def ComputableEvaluation : Prop :=
  ∀ (f : Nat → Nat), Computable f → StrictMono f → (∀ n, G n ≤ f n) →
    TerminalSemantics f ∧ EffectiveEvaluation f

/-- Full closed-evaluation clauses for both actual selected controls with no
supplied computational/termination/admissibility premise. -/
def SelectedClosedEvaluation : Prop :=
  (TerminalSemantics factorialControl ∧ EffectiveEvaluation factorialControl) ∧
  ∀ (b : Nat), TerminalSemantics (nearControl b) ∧ EffectiveEvaluation (nearControl b)

end LogicLineages.PermittedControl.Targets
