module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraph
open CommonLayerSyntax NormalForm SourceTermGraph

/-- Literal quantifier-free source grammar. Every nested Phi term is retained. -/
def test : SourceFormula → Bool
  | .equal _ _ | .less _ _ => true
  | .negative p => test p
  | .conjunction p q => test p && test q
  | .existsNat _ _ => false

/-- A single term tree gives disjoint graph allocation to both Boolean branches.
Its addition nodes join graph allocations, not source Boolean meanings. -/
def forest : SourceFormula → BaseTerm
  | .equal a b | .less a b => .add a b
  | .negative p => forest p
  | .conjunction p q => .add (forest p) (forest q)
  | .existsNat _ p => forest p

/-- Boolean polarity stays in the predicate. Total functional graph constraints
are conjoined outside it, so negation never negates a witness graph. -/
def predicate (start : Nat) : SourceFormula → NormalForm.Formula
  | .equal a b => SourceRows.relation false (output start a)
      (output (start + nodeCount a) b)
  | .less a b => SourceRows.relation true (output start a)
      (output (start + nodeCount a) b)
  | .negative p => .negative (predicate start p)
  | .conjunction p q => .conjunction (predicate start p)
      (predicate (start + nodeCount (forest p)) q)
  | .existsNat _ _ => .falsity

def matrix (start : Nat) (p : SourceFormula) : NormalForm.Formula :=
  .conjunction (graph start (forest p)) (predicate start p)

def start (p : SourceFormula) : Nat := SourceRows.Code.bound (instructions (forest p))
def compile (p : SourceFormula) : NormalForm.Formula := matrix (start p) p

def decideExists (p : SourceFormula) : Option Bool :=
  if test p then some (PlainFrontier.answer (compile p)) else none

def decideForall (p : SourceFormula) : Option Bool :=
  (decideExists (.negative p)).map Bool.not

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraph
