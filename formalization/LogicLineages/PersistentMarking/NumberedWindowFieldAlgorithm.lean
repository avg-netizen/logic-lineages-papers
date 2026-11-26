module

public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
open NumberedWindowPairAlgorithm (pair decode)

def pack : List Nat → Nat
  | [] => 0
  | x :: xs => pair x (pack xs) + 1

abbrev State := Option (Nat × List Nat)

def step : State → State
  | none => none
  | some (0, acc) => some (0, acc)
  | some (n+1, acc) => do
    let (head, tail) ← decode n
    pure (tail, head :: acc)

def steps : Nat → State → State
  | 0, s => s
  | fuel+1, s => steps fuel (step s)

def finish (s : State) : Option (List Nat) := do
  let (rest, acc) ← s
  if rest = 0 then some acc.reverse else none

def unpack (n : Nat) := finish (steps n (some (n, [])))

def packNode (tag : Nat) (xs : List Nat) := pair tag (pack xs) + 1

def unpackNode : Nat → Option (Nat × List Nat)
  | 0 => none
  | n+1 => do
    let (tag, body) ← decode n
    let xs ← unpack body
    pure (tag, xs)

end LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
