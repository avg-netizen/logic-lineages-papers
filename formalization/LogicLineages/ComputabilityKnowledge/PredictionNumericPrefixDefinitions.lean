module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetDefinitions
@[expose] public section
/-! Uniform numeric finite-table assembly of a constant left-prefix around
an existing body. No body semantics or runtime is postulated here. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionNumericPrefix
open Turing PredictionFiniteAlphabet

def entryState (p : Table) (q n : Nat) : Nat := if n = 0 then p.2.1 else q + 2 * n - 1

def prefixEntry (p : Table) (q : Nat) (word : List Nat) (r : Nat) : Nat × Action :=
  if r % 2 = 1 then (q + r - 1, .inl false)
  else (if r = 0 then p.2.1 else q + r - 1, .inr (word.getI (r / 2)))

def bodyRows (p : Table) (q : Nat) : List (Option (Nat × Action)) :=
  p.2.2 ++ (List.range (q * width p - p.2.2.length)).map (fun _ => none)

def prefixRows (p : Table) (q : Nat) (word : List Nat) : List (Option (Nat × Action)) :=
  (List.range (2 * word.length * width p)).map (fun i => some (prefixEntry p q word (i / width p)))

def assembled (p : Table) (q : Nat) (word : List Nat) : Table :=
  (p.1, entryState p q word.length, bodyRows p q ++ prefixRows p q word)

def code (p : Table) (q : Nat) (word : List Nat) : Nat := Encodable.encode (assembled p q word)

def machine (p : Table) (q : Nat) (word : List Nat) : TM0.Machine (Fin (width p)) Nat :=
  PredictionFiniteAlphabet.machine (assembled p q word)

end LogicLineages.ComputabilityKnowledge.PredictionNumericPrefix
