module
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions

@[expose] public section

/-! Explicit numerical merge of raw hereditary-CNF lists. The coefficient
argument to encodedNodeCode is stored minus one, as in the fixed codec.
Recursive sum calls have smaller paired-input indices, so a finite prefix
table supplies the exact operation without any arithmetic oracle. -/

namespace LogicLineages.OrdinalComparison

def encodedNodeCode (e c t : Nat) : Nat := Nat.pair e (Nat.pair c t) + 1

def encodedNaturalSumStep (n : Nat) (table : List Nat) : Nat :=
  let a := n.unpair.1
  let b := n.unpair.2
  if a = 0 then b
  else if b = 0 then a
  else
    let left := a.pred.unpair
    let right := b.pred.unpair
    let c := left.2.unpair.1
    let t := left.2.unpair.2
    let d := right.2.unpair.1
    let u := right.2.unpair.2
    let order := rawComparisonCode left.1 right.1
    if order = 0 then
      encodedNodeCode right.1 d (table.getD (Nat.pair a u) 0)
    else if order = 1 then
      encodedNodeCode left.1 (c + d + 1) (table.getD (Nat.pair t u) 0)
    else encodedNodeCode left.1 c (table.getD (Nat.pair t b) 0)

def encodedNaturalSumTable : Nat → List Nat
  | 0 => [0]
  | n + 1 => encodedNaturalSumTable n ++ [encodedNaturalSumStep (n + 1) (encodedNaturalSumTable n)]

def encodedNaturalSum (a b : Nat) : Nat :=
  (encodedNaturalSumTable (Nat.pair a b)).getD (Nat.pair a b) 0

end LogicLineages.OrdinalComparison
