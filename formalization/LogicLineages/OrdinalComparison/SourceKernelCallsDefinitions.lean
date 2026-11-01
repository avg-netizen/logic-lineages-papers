module
public import LogicLineages.OrdinalComparison.SourcePeakCallsDefinitions
public import LogicLineages.OrdinalComparison.SuccessorNormalizationDefinitions
public import Mathlib.Logic.Relation

@[expose] public section
namespace LogicLineages.OrdinalComparison

def comparisonLiteralInner : List (NONote × Nat) → FixedLimitPositiveExpr → OneVariableComparisonExpr
  | [],E => .positive E
  | p::w,E => .range (p::w) E

def encodedComparisonStripOuter (n : Nat) : Nat :=
  if n%2=0 then n else
    let p := (n/2).unpair
    let word := ((Encodable.decode (α := List (Nat × Nat)) p.1).getD []).reverse.tail.reverse
    if word=[] then 2*p.2 else 2*Nat.pair (Encodable.encode word) p.2+1

end LogicLineages.OrdinalComparison
