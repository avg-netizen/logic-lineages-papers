module
public import LogicLineages.OrdinalComparison.EncodedNaturalSumDefinitions

@[expose] public section

/-! Explicit numerical paired-monomial product. All exponent sums and final
collection use the fixed numerical natural-sum algorithm. A monomial parameter
is encoded as (raw exponent code, coefficient minus one); its product table is
indexed by that parameter paired with the raw right-input code. The outer
product table then recurses on the left tail. No arithmetic supplier or
computation certificate is a definition field. -/

namespace LogicLineages.OrdinalComparison

def encodedMonomialProductStep (n : Nat) (table : List Nat) : Nat :=
  let parameter := n.unpair.1
  let b := n.unpair.2
  if b = 0 then 0
  else
    let fields := b.pred.unpair
    let exponent := encodedNaturalSum parameter.unpair.1 fields.1
    let coefficient := (parameter.unpair.2 + 1) * (fields.2.unpair.1 + 1) - 1
    let node := encodedNodeCode exponent coefficient 0
    encodedNaturalSum node (table.getD (Nat.pair parameter fields.2.unpair.2) 0)

def encodedMonomialProductTable : Nat → List Nat
  | 0 => [0]
  | n + 1 => encodedMonomialProductTable n ++
      [encodedMonomialProductStep (n + 1) (encodedMonomialProductTable n)]

def encodedMonomialProduct (e c b : Nat) : Nat :=
  let n := Nat.pair (Nat.pair e c) b
  (encodedMonomialProductTable n).getD n 0

def encodedNaturalProductStep (n : Nat) (table : List Nat) : Nat :=
  let a := n.unpair.1
  let b := n.unpair.2
  if a = 0 then 0
  else
    let fields := a.pred.unpair
    encodedNaturalSum (encodedMonomialProduct fields.1 fields.2.unpair.1 b)
      (table.getD (Nat.pair fields.2.unpair.2 b) 0)

def encodedNaturalProductTable : Nat → List Nat
  | 0 => [0]
  | n + 1 => encodedNaturalProductTable n ++
      [encodedNaturalProductStep (n + 1) (encodedNaturalProductTable n)]

def encodedNaturalProduct (a b : Nat) : Nat :=
  (encodedNaturalProductTable (Nat.pair a b)).getD (Nat.pair a b) 0

end LogicLineages.OrdinalComparison
