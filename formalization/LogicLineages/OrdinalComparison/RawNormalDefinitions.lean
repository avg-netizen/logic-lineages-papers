module
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions

@[expose] public section

/-! A finite-table normal-form recognizer on the fixed raw code. The ordinal
normality predicate itself remains Mathlib's NF; this numerical function only
tests child normality and strict leading-exponent descent. Correspondence and
primitive recursion are separate obligations. -/

namespace LogicLineages.OrdinalComparison

def rawNormalStep (n : Nat) (table : List Nat) : Nat :=
  if n = 0 then 1
  else
    let fields := n.pred.unpair
    let e := fields.1
    let t := fields.2.unpair.2
    if table.getD e 0 = 1 ∧ table.getD t 0 = 1 ∧
      (t = 0 ∨ rawComparisonCode t.pred.unpair.1 e = 0) then 1 else 0

def rawNormalTable : Nat → List Nat
  | 0 => [1]
  | n + 1 => rawNormalTable n ++ [rawNormalStep (n + 1) (rawNormalTable n)]

def rawNormalCode (n : Nat) : Nat := (rawNormalTable n).getD n 0

end LogicLineages.OrdinalComparison
