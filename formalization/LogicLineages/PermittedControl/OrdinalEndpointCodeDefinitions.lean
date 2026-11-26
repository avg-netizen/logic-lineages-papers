module
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Constructor uses a positive coefficient stored minus one. -/
def ordinalNodeCode (e c t : Nat) : Nat := Nat.pair e (Nat.pair c t)+1

/-- Literal numeric implementation of Mathlib ONote.addAux. -/
def ordinalAddAuxCode (e c z : Nat) : Nat :=
  if z=0 then ordinalNodeCode e c 0 else
  let v := z-1
  let cmp := rawComparisonCode e v.unpair.1
  if cmp=0 then z else
  if cmp=1 then ordinalNodeCode e (c+v.unpair.2.unpair.1+1) v.unpair.2.unpair.2
  else ordinalNodeCode e c z

/-- One paired-input table entry; recursive addition is through the left tail. -/
def ordinalAddCodeStep (n : Nat) (table : List Nat) : Nat :=
  let a := n.unpair.1
  let b := n.unpair.2
  if a=0 then b else
  let u := a-1
  ordinalAddAuxCode u.unpair.1 u.unpair.2.unpair.1
    (table.getD (Nat.pair u.unpair.2.unpair.2 b) 0)

def ordinalAddCodeTable : Nat → List Nat
  | 0 => []
  | n+1 => ordinalAddCodeTable n ++ [ordinalAddCodeStep n (ordinalAddCodeTable n)]

def ordinalAddCode (a b : Nat) : Nat :=
  (ordinalAddCodeTable (Nat.pair a b+1)).getD (Nat.pair a b) 0

/-- Literal numeric implementation of Mathlib ONote.sub. Recursion is only
when both leading exponents and positive coefficients agree exactly. -/
def ordinalSubCodeStep (n : Nat) (table : List Nat) : Nat :=
  let a := n.unpair.1
  let b := n.unpair.2
  if a=0 then 0 else if b=0 then a else
  let u := a-1
  let v := b-1
  let cmp := rawComparisonCode u.unpair.1 v.unpair.1
  if cmp=0 then 0 else if cmp=2 then a else
  let c := u.unpair.2.unpair.1
  let d := v.unpair.2.unpair.1
  if c=d then table.getD (Nat.pair u.unpair.2.unpair.2 v.unpair.2.unpair.2) 0
  else if d<c then ordinalNodeCode u.unpair.1 (c-d-1) u.unpair.2.unpair.2
  else 0

def ordinalSubCodeTable : Nat → List Nat
  | 0 => []
  | n+1 => ordinalSubCodeTable n ++ [ordinalSubCodeStep n (ordinalSubCodeTable n)]

def ordinalSubCode (a b : Nat) : Nat :=
  (ordinalSubCodeTable (Nat.pair a b+1)).getD (Nat.pair a b) 0

end LogicLineages.PermittedControl
