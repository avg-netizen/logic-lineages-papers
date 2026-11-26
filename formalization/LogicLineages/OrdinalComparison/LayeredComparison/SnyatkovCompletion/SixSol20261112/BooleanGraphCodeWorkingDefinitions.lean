module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCode
open NonlinearProjectionCompletion

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

def forest (code : Nat) : Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 then 0
  else if code % 8 = 2 ∨ code % 8 = 3 then
    WindowCode.add (code / 8).unpair.1 (code / 8).unpair.2
  else if code % 8 = 4 then (code / 8).unpair.2
  else if code % 8 = 5 then forest (code / 8)
  else WindowCode.add (forest (code / 8).unpair.1) (forest (code / 8).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
    have hl := Nat.unpair_left_le (code / 8)
    have hr := Nat.unpair_right_le (code / 8)
    omega

def predicate (start code : Nat) : Nat :=
  if code % 8 = 0 then 0
  else if code % 8 = 1 then 1
  else if code % 8 = 2 ∨ code % 8 = 3 then
    SourceRows.Code.relation (code % 8 == 3)
      (ExpandedGraphCode.output start (code / 8).unpair.1)
      (ExpandedGraphCode.output
        (start + ExpandedGraphCode.nodeCount (code / 8).unpair.1) (code / 8).unpair.2)
  else if code % 8 = 4 then
    let m := (code / 8).unpair.1
    let x := ExpandedGraphCode.output start (code / 8).unpair.2
    if m = 0 then SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData x)])
    else 6 * Encodable.encode ((1, m - 1, (0 : Int), [((1 : Int), SourceTermGraph.Code.variableData x)]) : NormalForm.Code.AtomData) + 2
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

def startFor (bound : List Nat) (code : Nat) : Nat :=
  (bound ++ termVariables (forest code)).foldr max 0 + 1

def allocated (bound : List Nat) (code : Nat) : List Nat :=
  ExpandedGraphCode.allocated (startFor bound code) (forest code)

def compile (bound : List Nat) (code : Nat) : Nat :=
  SourceTermGraph.Code.conjunction
    (ExpandedGraphCode.graph (startFor bound code) (forest code))
    (predicate (startFor bound code) code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCode
