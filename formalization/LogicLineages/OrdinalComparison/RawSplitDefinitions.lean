module
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions
public import Mathlib.Data.List.GetD

@[expose] public section

/-! Numerical version of ONote.split: return a paired limit-part code and
natural finite tail. A raw zero exponent ends the suffix just as in the literal
source split, including on nonnormal inputs. Table correctness is a separate
target; this definition does not inspect actual ordinal values. -/

namespace LogicLineages.OrdinalComparison

def rawSplitStep (n : Nat) (table : List Nat) : Nat :=
  if n = 0 then 0
  else
    let fields := n.pred.unpair
    let e := fields.1
    let c := fields.2.unpair.1
    let t := fields.2.unpair.2
    if e = 0 then Nat.pair 0 (c + 1)
    else
      let tail := (table.getD t 0).unpair
      Nat.pair (Nat.pair e (Nat.pair c tail.1) + 1) tail.2

def rawSplitTable : Nat → List Nat
  | 0 => [0]
  | n + 1 => rawSplitTable n ++ [rawSplitStep (n + 1) (rawSplitTable n)]

def rawSplitCode (n : Nat) : Nat := (rawSplitTable n).getD n 0

end LogicLineages.OrdinalComparison
