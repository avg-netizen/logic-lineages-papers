module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphTargets
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization

/-- Actual local inverse/zero conventions and total uniquely valued term graphs. -/
def TermGraphs : Prop :=
  ExpandedGraphTargets.LiteralSubtraction ∧ ExpandedGraphTargets.LiteralDivision ∧
  ExpandedGraphTargets.LiteralInverse ∧ ExpandedGraphTargets.ExactAllocation ∧
  ExpandedGraphTargets.ExactGraphSupport ∧ ExpandedGraphTargets.PlainOriginalGraphClass ∧
  ExpandedGraphTargets.GraphSoundness ∧ ExpandedGraphTargets.TotalGraphRealization ∧
  ExpandedGraphTargets.AllocatedNodeUniqueness

/-- The total forest is outside the arbitrary Boolean skeleton, including negation. -/
def MatrixGraphs : Prop :=
  ExpandedBooleanGraphTargets.LiteralForestSupport ∧ ExpandedBooleanGraphTargets.HFreeOriginalForest ∧
  ExpandedBooleanGraphTargets.ActualPredicateInterpretation ∧ ExpandedBooleanGraphTargets.ExactFreshGraphNames ∧
  ExpandedBooleanGraphTargets.OriginalGraphNameSupport ∧ ExpandedBooleanGraphTargets.LiteralZeroShiftGraphClass ∧
  ExpandedBooleanGraphTargets.ActualExpandedMatrixGraph

/-- No caller supplies allowedness, a graph witness or parameter independence. -/
def AllowedWholeBlock : Prop := ∀ (i : Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true →
  (OriginalSourceElimination.binderBlock i p).Nodup ∧
  TiedLinear.allowed (OriginalSourceElimination.binderBlock i p) (normalized i p) = true ∧
  BlockRows.ParametersIndependent (OriginalSourceElimination.binderBlock i p) (normalized i p) ∧
  PlainBlockSplit.formulaHFree (normalized i p) = true ∧
  ∀ ν : Nat → Nat,
    (PlainBlockSplit.existsPrefix ν (OriginalSourceElimination.binderBlock i p) (normalized i p) ↔
      ∃ n : Nat, p.eval (Function.update ν i n))

def OriginalSupport : Prop := ∀ (i : Nat) (p : Matrix),
  PlainBlockSplit.matrixHFree p = true →
  (∀ j ∈ OriginalSourceElimination.graphNames i p, j ≠ i ∧ j ∉ p.variables) ∧
  ∀ j ∈ (normalized i p).variables,
    j ∈ p.variables ∨ j ∈ OriginalSourceElimination.graphNames i p

/-- Literal data equality on every typed input, independent of H-free semantic admission. -/
def LiteralCode : Prop :=
  (∀ t : Term, Code.termVariables t.encode = t.variables) ∧
  (∀ p : Matrix, Code.matrixVariables p.encode = p.variables ∧
    Code.forest p.encode = (ExpandedBooleanGraph.forest p).encode) ∧
  (∀ (start : Nat) (p : Matrix),
    Code.predicate start p.encode = (ExpandedBooleanGraph.predicate start p).encode) ∧
  (∀ (i : Nat) (p : Matrix),
    Code.names i p.encode = OriginalSourceElimination.graphNames i p ∧
    Code.graphFormula i p.encode = (OriginalSourceElimination.graphFormula i p).encode ∧
    Code.program i p.encode = (OriginalSourceElimination.binderBlock i p,
      BlockFormulaSubstitutionCode.formulaCode (normalized i p)))

/-- Genuine total numeric programs, not a supplied semantic normalizer. -/
def Programs : Prop := Computable Code.termVariables ∧ Computable Code.matrixVariables ∧
  Computable Code.forest ∧ Computable₂ Code.predicate ∧ Computable₂ Code.names ∧
  Computable₂ Code.graphFormula ∧ Computable₂ Code.program

def Full : Prop := TermGraphs ∧ MatrixGraphs ∧ AllowedWholeBlock ∧ OriginalSupport ∧ LiteralCode ∧ Programs
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationTargets
