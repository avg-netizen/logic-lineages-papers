module
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions
public import Mathlib.Data.List.GetD

@[expose] public section

/-! A course-of-values table for the literal raw CNF comparison. The table is
indexed by pairs of raw natural codes, not by ordinal values. Its entries use
0/1/2 for lt/eq/gt. Both recursive child pairs have strictly smaller pairing
indices. No normality assumption is needed for syntax-level correspondence.
This supplies an explicit numerical algorithm; correctness and primitive
recursion are separate targets. -/

namespace LogicLineages.OrdinalComparison

def orderingCode : Ordering → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

def rawComparisonStep (n : Nat) (table : List Nat) : Nat :=
  let a := n.unpair.1
  let b := n.unpair.2
  if a = 0 then if b = 0 then 1 else 0
  else if b = 0 then 2
  else
    let left := a.pred.unpair
    let right := b.pred.unpair
    let exponent := table.getD (Nat.pair left.1 right.1) 1
    if exponent = 1 then
      if left.2.unpair.1 < right.2.unpair.1 then 0
      else if right.2.unpair.1 < left.2.unpair.1 then 2
      else table.getD (Nat.pair left.2.unpair.2 right.2.unpair.2) 1
    else exponent

def rawComparisonTable : Nat → List Nat
  | 0 => [1]
  | n + 1 => rawComparisonTable n ++ [rawComparisonStep (n + 1) (rawComparisonTable n)]

def rawComparisonCode (a b : Nat) : Nat :=
  (rawComparisonTable (Nat.pair a b)).getD (Nat.pair a b) 1

end LogicLineages.OrdinalComparison
