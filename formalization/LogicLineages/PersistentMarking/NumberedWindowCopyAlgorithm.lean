module

public import LogicLineages.PersistentMarking.NumberedWindowOwnerAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCopyAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowOwnerAlgorithm (copies)
open NumberedWindowMarkRootAlgorithm (guarded)

abbrev Entries := List (Nat × Nat)

def lookup (xs : Entries) (name : Nat) : Option (Nat × Nat) :=
  xs.foldr (fun entry tail =>
    if name = entry.1 then some (entry.2,0) else tail.map (fun p => (p.1,p.2+1))) none

def rankParts (xs : Entries) (tag payload : Nat) : Option Nat :=
  if tag < 4 then some 1 else if tag = 4 then some 0 else if tag = 5 then do
    let (name,arity) ← decode payload
    let (declared,i) ← lookup xs name
    if arity = declared then some (i+2) else none
  else none

def rank (xs : Entries) (head : Nat) : Option Nat :=
  (decode head).bind (fun p => rankParts xs p.1 p.2)

def compareRanks (smaller : Bool) (xs : Entries) (f g : Nat) : Bool :=
  (rank xs f).any (fun m => (rank xs g).any (fun n =>
    if smaller then decide (n < m) else decide (m = n)))

def allowedTarget (smaller : Bool) (xs : Entries) (heads : List Nat) (result f g : Nat) :=
  result == (declaration g).1 && compareRanks smaller xs f g && heads.contains g

def copyRows (xs : Entries) (heads : List Nat) (q r : Nat × List Nat) :=
  let a (i : Nat) := q.2.getD i 0
  let g := r.2.getD 0 0
  q.1 == 5 && r.1 == 4 && a 2 != 0 &&
    (allowedTarget true xs heads (a 1) (a 0) g &&
     copies (a 0) (a 2).pred (a 3) (a 4) (declaration g).2 == r.2.getD 1 0)

def copy (xs : Entries) (heads : List Nat) (src dst : Nat) :=
  guarded src dst ((unpackNode src).any (fun q => (unpackNode dst).any (copyRows xs heads q)))

end LogicLineages.PersistentMarking.NumberedWindowCopyAlgorithm
