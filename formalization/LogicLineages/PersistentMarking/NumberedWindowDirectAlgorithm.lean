module

public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
public import Init.Data.List.Perm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm
open NumberedWindowFieldAlgorithm

abbrev Entry := Nat × Nat × Nat
abbrev Witness := List Nat × List Nat × List Entry

def readEntry (code : Nat) : Option Entry := do
  let (4, [target, dominator, cert]) ← unpackNode code | none
  pure (target, dominator, cert)

def entries : List Nat → Option (List Entry)
  | [] => some []
  | n :: ns => do
    let e ← readEntry n
    let es ← entries ns
    pure (e :: es)

def readWitness (code : Nat) : Option Witness := do
  let (5, [k, r, a]) ← unpackNode code | none
  let kept ← unpack k
  let removed ← unpack r
  let inputs ← unpack a
  let added ← entries inputs
  pure (kept, removed, added)

def typedList (scalar : Nat → Bool) (code : Nat) : Bool :=
  match unpack code with
  | none => false
  | some xs => xs.all scalar

def directLists (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (source target : List Nat) (w : Witness) : Bool :=
  source.all scalar && target.all scalar &&
    decide (source.Perm (w.1 ++ w.2.1)) &&
    decide (target.Perm (w.1 ++ w.2.2.map Prod.fst)) &&
    !w.2.1.isEmpty &&
    w.2.2.all (fun e => decide (e.2.1 ∈ w.2.1) && positive e.2.1 e.2.2 e.1)

def direct (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    (src cert dst : Nat) : Bool :=
  match unpack src, readWitness cert, unpack dst with
  | some xs, some w, some ys => directLists scalar positive xs ys w
  | _, _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm
