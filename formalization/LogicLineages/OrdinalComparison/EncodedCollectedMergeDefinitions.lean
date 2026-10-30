module
public import LogicLineages.OrdinalComparison.CollectedMergeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def encodedCollectedCons (key coefficient rest : Nat) : Nat :=
  1 + Nat.pair key (Nat.pair coefficient rest)

/-- Literal code-order insertion. Recursive tail values are looked up only in
an already computed finite table; the decrease is separately proved. -/
def encodedCollectedInsertStep (key a n : Nat) (table : List Nat) : Nat :=
  if a=0 then n
  else if n=0 then encodedCollectedCons key a 0
  else
    let p := n.pred.unpair
    let fields := p.2.unpair
    if key<p.1 then encodedCollectedCons key a n
    else if key=p.1 then encodedCollectedCons p.1 (a+fields.1) fields.2
    else encodedCollectedCons p.1 fields.1 (table.getD fields.2 0)

def encodedCollectedInsertTable (key a : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => encodedCollectedInsertTable key a n ++
      [encodedCollectedInsertStep key a n (encodedCollectedInsertTable key a n)]

def encodedCollectedInsert (key a n : Nat) : Nat :=
  (encodedCollectedInsertTable key a (n+1)).getD n 0

def encodedCollectedMergeStep (right n : Nat) (table : List Nat) : Nat :=
  if n=0 then right else
    let p := n.pred.unpair
    let fields := p.2.unpair
    encodedCollectedInsert p.1 fields.1 (table.getD fields.2 0)

def encodedCollectedMergeTable (right : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => encodedCollectedMergeTable right n ++
      [encodedCollectedMergeStep right n (encodedCollectedMergeTable right n)]

def encodedCollectedMerge (left right : Nat) : Nat :=
  (encodedCollectedMergeTable right (left+1)).getD left 0

def encodedCollectedAdd (left right : Nat) : Nat :=
  let l := left.unpair
  let r := right.unpair
  Nat.pair (l.1+r.1) (Nat.pair (l.2.unpair.1+r.2.unpair.1)
    (encodedCollectedMerge l.2.unpair.2 r.2.unpair.2))

end LogicLineages.OrdinalComparison
