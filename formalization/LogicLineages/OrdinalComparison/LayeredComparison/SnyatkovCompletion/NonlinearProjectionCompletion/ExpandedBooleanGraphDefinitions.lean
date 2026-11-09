module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraph
open NormalForm

/-- All term occurrences, including both disjuncts and negated subformulas,
are assigned total functional graphs outside the Boolean predicate. -/
def forest : Matrix → Term
  | .truth | .falsity => .numeral 0
  | .equal a b | .less a b => .add a b
  | .divisible _ a => a
  | .negative p => forest p
  | .conjunction p q | .disjunction p q => .add (forest p) (forest q)

def predicate (start : Nat) : Matrix → NormalForm.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .equal a b => SourceRows.relation false (ExpandedGraph.output start a)
      (ExpandedGraph.output (start + ExpandedGraph.nodeCount a) b)
  | .less a b => SourceRows.relation true (ExpandedGraph.output start a)
      (ExpandedGraph.output (start + ExpandedGraph.nodeCount a) b)
  | .divisible m a =>
      if m = 0 then ExpandedGraph.equation (0, [(1, .variable (ExpandedGraph.output start a))])
      else .atom (.divisible (m - 1) (0, [(1, .variable (ExpandedGraph.output start a))]))
  | .negative p => .negative (predicate start p)
  | .conjunction p q => .conjunction (predicate start p)
      (predicate (start + ExpandedGraph.nodeCount (forest p)) q)
  | .disjunction p q => .disjunction (predicate start p)
      (predicate (start + ExpandedGraph.nodeCount (forest p)) q)

def matrix (start : Nat) (p : Matrix) : NormalForm.Formula :=
  .conjunction (ExpandedGraph.graph start (forest p)) (predicate start p)
def startFor (bound : List Nat) (p : Matrix) : Nat :=
  (bound ++ p.variables).foldr max 0 + 1
def allocated (bound : List Nat) (p : Matrix) : List Nat :=
  ExpandedGraph.allocated (startFor bound p) (forest p)
def compile (bound : List Nat) (p : Matrix) : NormalForm.Formula := matrix (startFor bound p) p

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraph
