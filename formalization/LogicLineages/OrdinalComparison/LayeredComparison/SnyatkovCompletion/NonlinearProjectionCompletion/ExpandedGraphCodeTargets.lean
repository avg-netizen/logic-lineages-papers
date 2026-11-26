module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeTargets
open ExpandedGraphCode

/-- Every expanded constructor, including both unsupported H constructors. -/
def LiteralNodeCount : Prop := ∀ t : Term, nodeCount t.encode = ExpandedGraph.nodeCount t

def LiteralAllocation : Prop := ∀ (start : Nat) (t : Term),
  allocated start t.encode = ExpandedGraph.allocated start t ∧
  output start t.encode = ExpandedGraph.output start t

/-- Exact signed rows and original local formulas, including zero division. -/
def LiteralLocalClauses : Prop :=
  (∀ z x c : Nat, multiplyRow z x c = NormalForm.rowData (ExpandedGraph.multiplyRow z x c)) ∧
  (∀ z x y : Nat, subtraction z x y = (ExpandedGraph.subtraction z x y).encode) ∧
  (∀ z x c : Nat, division z x c = (ExpandedGraph.division z x c).encode) ∧
  (∀ u z x : Nat, inverse u z x = (ExpandedGraph.inverse u z x).encode)

/-- Literal syntax calibration has no freshness or H-free premise. Unsupported
H syntax produces the same explicit falsity as the original typed compiler. -/
def LiteralGraphCalibration : Prop := ∀ (start : Nat) (t : Term),
  graph start t.encode = (ExpandedGraph.graph start t).encode

def ActualAllocationPrograms : Prop :=
  Computable nodeCount ∧ Computable₂ allocated ∧ Computable₂ output

/-- All local clauses and the recursive graph are actual closed programs,
with arbitrary numeric runtime arguments and no supplied effectiveness premise. -/
def ActualGraphPrograms : Prop :=
  Computable (fun p : Nat × Nat × Nat => multiplyRow p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => subtraction p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => division p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => inverse p.1 p.2.1 p.2.2) ∧
  Computable₂ graph

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeTargets
