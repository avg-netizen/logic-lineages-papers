module

public import LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowAddressAlgorithm (addressView)

abbrev RawEdge := Nat × Nat × Nat
abbrev ClassHop := Nat × RawEdge
abbrev Least := List Nat → Nat → Nat → Option Nat
abbrev Step := List Nat → Nat → Nat → Nat → Nat → Bool

/-- Only the envelope is read here. The raw-step callback checks the witness and both raw terms. -/
def edgeView (code : Nat) : Option RawEdge := do
  let (1,[q,r,w]) ← unpackNode code | none
  pure (q,w,r)

def hopView (code : Nat) : Option ClassHop := do
  let (2,[target,edge]) ← unpackNode code | none
  let row ← edgeView edge
  pure (target,row)

def advance (step : Nat → Nat → Nat → Bool) (least : Nat → Option Nat)
    (source : Option Nat) (code : Nat) : Option Nat := do
  let current ← source
  let (target,q,w,r) ← hopView code
  if step q w r && (least q == some current) && (least r == some target) then
    some target
  else none

def walk (step : Nat → Nat → Nat → Bool) (least : Nat → Option Nat)
    (source : Nat) (codes : List Nat) (target : Nat) : Bool :=
  codes.foldl (advance step least) (some source) == some target

def positive (step : Step) (least : Least) (ctx : List Nat) (ty source cert target : Nat) : Bool :=
  (unpack cert).any (fun codes => !codes.isEmpty &&
    walk (step ctx ty) (least ctx ty) source codes target)

def addressRS (step : Step) (least : Least) (source cert target : Nat) : Bool :=
  match addressView source, addressView target with
  | some (sc,st,s), some (tc,tt,t) =>
    (sc == tc) && (st == tt) && positive step least sc st s cert t
  | _, _ => false

end LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm
