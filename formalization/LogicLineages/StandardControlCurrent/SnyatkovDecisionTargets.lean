module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionWorkingDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.StandardControlCurrent.SnyatkovDecisionTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open SixSol20261112

/-- The original variable-seed hierarchy, literal fixed control, and actual
computability of the control and its finite-search floor inverse. -/
def ControlArithmetic : Prop :=
  (∀ n : Nat, fastControl 0 n = 2 ^ n) ∧
  (∀ j n : Nat, fastControl (j + 1) n = (fastControl j)^[n + 1] n) ∧
  (∀ n : Nat, Phi n = fastControl 5 (n + 100)) ∧
  Computable Phi ∧ Computable LayeredComparison.SnyatkovInverse.phiInverse

/-- The reused raw binder equals the current graph-and-projector composition
literally on every encoded Matrix, not just on semantically admitted inputs.
The original binder name is prepended to the list of auxiliary graph names. -/
def CurrentBinderCompatibility : Prop := ∀ (i : Nat) (p : Matrix),
  SourceDecision.binder i p.encode =
    WholeBoundProjectionCode.project
      (i :: HFreeGraphNormalization.Code.names i p.encode)
      (HFreeGraphNormalization.Code.graphFormula i p.encode)

/-- The actual all-code compiler and its typed literal/semantic calibration
for every original source formula, at every valuation. No shape restriction. -/
def EffectiveOriginalElimination : Prop :=
  Computable SourceDecision.eliminate ∧
  ∀ p : SourceFormula,
    SourceDecision.eliminate p.encode = (OriginalSourceElimination.eliminate p).encode ∧
    PlainBlockSplit.matrixHFree (OriginalSourceElimination.eliminate p) = true ∧
    (∀ i ∈ (OriginalSourceElimination.eliminate p).variables, i ∈ p.variables) ∧
    ∀ ν : Nat → Nat, (OriginalSourceElimination.eliminate p).eval ν ↔ p.eval ν

/-- An actual total quantifier-free evaluator at zero. Its calibrated
domain is all typed matrices, so in particular the closed H-free outputs.
This does not assert quantifier elimination in the expanded language. -/
def ZeroEvaluator : Prop :=
  Computable SourceDecision.groundTerm ∧ Computable SourceDecision.groundMatrix ∧
  (∀ t : Term, SourceDecision.groundTerm t.encode = t.value (fun _ => 0)) ∧
  ∀ p : Matrix, SourceDecision.groundMatrix p.encode = true ↔ p.eval (fun _ => 0)

/-- The literal program is total on all codes. Its decision claim is the
original closed-sentence domain, with no further source admission filter. -/
def ActualClosedAnswer : Prop :=
  Computable SourceDecision.answer ∧
  ∀ p : SourceFormula, p.variables = [] → ∀ ν : Nat → Nat,
    SourceDecision.answer p.encode = true ↔ p.eval ν

/-- Paper18 m:thm:snyatkov, control.tex 66–69: effective decidability of
the complete first-order theory of (Nat; 0, 1, +, <, Phi). -/
def FullSourceDecision : Prop :=
  ∃ answer : Nat → Bool, Computable answer ∧
    ∀ p : SourceFormula, p.variables = [] → ∀ ν : Nat → Nat,
      answer p.encode = true ↔ p.eval ν

end LogicLineages.StandardControlCurrent.SnyatkovDecisionTargets
