module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeCode

open RawSourceDAG
open LogicLineages.OrdinalComparison.Source

def nodeCode (a : Node) (tail : List Nat) : Nat :=
  let tag := a.2.2.1
  let x := a.2.2.2.getD 0 0
  let y := a.2.2.2.getD 1 0
  let z := a.2.2.2.getD 2 0
  if tag = 0 then 8 * x else
  if tag = 1 then 8 * Nat.pair (tail.getD y 7) (tail.getD z 7) + 5 else
  if tag = 2 then 8 * Nat.pair x (tail.getD z 7) + 6 else
  if tag = 3 then 1 else
  if tag = 4 then 2 else
  if tag = 5 then 8 * x + 3 else
  if tag = 6 then 8 * x + 4 else 7

def table (nodes : List Node) : List Nat :=
  nodes.foldr (fun a tail => nodeCode a tail :: tail) []

def expand (c : Code) : Nat := (table c.2.1).getD c.2.2.1 7

end LogicLineages.ControlSensitivityCurrent.CurrentTreeCode
