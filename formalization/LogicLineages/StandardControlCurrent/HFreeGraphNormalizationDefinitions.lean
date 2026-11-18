module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.OriginalSourceEliminationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCodeDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalization
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion

def normalized (i : Nat) (p : Matrix) : BlockRows.Formula :=
  WholeBoundInitialization.«initialize» (OriginalSourceElimination.binderBlock i p)
    (OriginalSourceElimination.graphFormula i p)

namespace Code
/-- Total raw variable traversal; every literal occurrence is retained. -/
def termVariables (code : Nat) : List Nat :=
  if code % 10 = 0 then []
  else if code % 10 = 1 then [code / 10]
  else if code % 10 = 2 ∨ code % 10 = 3 then
    termVariables (code / 10).unpair.1 ++ termVariables (code / 10).unpair.2
  else if code % 10 = 4 ∨ code % 10 = 5 then termVariables (code / 10).unpair.2
  else termVariables (code / 10)
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 10 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 10)
    have hr := Nat.unpair_right_le (code / 10)
    omega

def matrixVariables (code : Nat) : List Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 then []
  else if code % 8 = 2 ∨ code % 8 = 3 then
    termVariables (code / 8).unpair.1 ++ termVariables (code / 8).unpair.2
  else if code % 8 = 4 then termVariables (code / 8).unpair.2
  else if code % 8 = 5 then matrixVariables (code / 8)
  else matrixVariables (code / 8).unpair.1 ++ matrixVariables (code / 8).unpair.2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    omega

/-- Literal joined forest, including graphs under negation and both Boolean branches. -/
def forest (code : Nat) : Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 then 0
  else if code % 8 = 2 ∨ code % 8 = 3 then 10 * (code / 8) + 2
  else if code % 8 = 4 then (code / 8).unpair.2
  else if code % 8 = 5 then forest (code / 8)
  else 10 * Nat.pair (forest (code / 8).unpair.1) (forest (code / 8).unpair.2) + 2
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    omega

/-- Raw normal-form predicate with positive divisors and explicit zero-divisor equality. -/
def predicate (start code : Nat) : Nat :=
  if code % 8 = 0 then 0
  else if code % 8 = 1 then 1
  else if code % 8 = 2 ∨ code % 8 = 3 then
    let a := (code / 8).unpair.1
    let b := (code / 8).unpair.2
    SourceRows.Code.relation (decide (code % 8 = 3)) (ExpandedGraphCode.output start a)
      (ExpandedGraphCode.output (start + ExpandedGraphCode.nodeCount a) b)
  else if code % 8 = 4 then
    let m := (code / 8).unpair.1
    let z := ExpandedGraphCode.output start (code / 8).unpair.2
    let row : NormalForm.Code.RowData := (0,[(1,SourceTermGraph.Code.variableData z)])
    if m = 0 then SourceTermGraph.Code.equation row
    else 6 * Encodable.encode ((1,m-1,row) : NormalForm.Code.AtomData) + 2
  else if code % 8 = 5 then 6 * predicate start (code / 8) + 3
  else 6 * Nat.pair (predicate start (code / 8).unpair.1)
    (predicate (start + ExpandedGraphCode.nodeCount (forest (code / 8).unpair.1))
      (code / 8).unpair.2) + (code % 8 - 2)
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    omega

def startFor (i code : Nat) : Nat := ([i] ++ matrixVariables code).foldr max 0 + 1
def names (i code : Nat) : List Nat := ExpandedGraphCode.allocated (startFor i code) (forest code)
def bound (i code : Nat) : List Nat := i :: names i code
def graphFormula (i code : Nat) : Nat :=
  SourceTermGraph.Code.conjunction (ExpandedGraphCode.graph (startFor i code) (forest code))
    (predicate (startFor i code) code)
/-- Actual raw whole-block initializer, with deterministic all-code traversal. -/
def program (i code : Nat) : List Nat × Nat :=
  (bound i code,WholeBoundInitializationCode.formula (bound i code) (graphFormula i code))
end Code
end LogicLineages.StandardControlCurrent.HFreeGraphNormalization
