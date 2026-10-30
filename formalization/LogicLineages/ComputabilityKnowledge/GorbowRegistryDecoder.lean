module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTuple
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-! Literal bounded decoders for the separate U/u registry tuple convention.
Pair search is finite; tuple evaluation iterates a concrete state transition
exactly the input code times. No choice or assumed decoding supplier occurs. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
open GorbowRegistryTuple

def pairCandidates (code : Nat) : List (Nat × Nat) :=
  (List.range (code+1)).flatMap (fun a => (List.range (code+1)).map (fun b => (a,b)))
def decodePair (code : Nat) : Option (Nat × Nat) :=
  (pairCandidates code).find? (fun p => decide (pair p.1 p.2 = code))

abbrev State := Option (Nat × List Nat)
def restore (acc : List Nat) (tail : Nat) : Nat := acc.foldl (fun c a => pair a c+1) tail

def tupleStep : State → State
  | none => none
  | some (0,acc) => some (0,acc)
  | some (c+1,acc) => do
    let (a,b) ← decodePair c
    pure (b,a::acc)

def decodeTuple (code : Nat) : Option (List Nat) := do
  let (rest,acc) ← tupleStep^[code] (some (code,[]))
  if rest=0 then some acc.reverse else none

def decodeHeader (code : Nat) : Option (Nat × Nat × List Nat) := do
  let (arity,body) ← decodePair code
  let (tag,argsCode) ← decodePair body
  let args ← decodeTuple argsCode
  pure (arity,tag,args)
end LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
