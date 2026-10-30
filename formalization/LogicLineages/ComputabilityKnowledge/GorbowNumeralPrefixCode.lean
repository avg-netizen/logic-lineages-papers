module

public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section
/-! Literal numeral-prefix recognition, distinct from arbitrary closed
arithmetic evaluation. A prefix parser retains its exact trailing suffix. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCode

def leadingSucc (raw : List Nat) : Nat :=
  raw.foldr (fun tag count => if tag=2 then count+1 else 0) 0

def parse (raw : List Nat) : Option (Nat × List Nat) :=
  let n := leadingSucc raw
  if raw[n]?=some 1 then some (n,raw.drop (n+1)) else none

def decode (raw : List Nat) : Option Nat := do
  let p ← parse raw
  if p.2=[] then some p.1 else none
end LogicLineages.ComputabilityKnowledge.GorbowNumeralPrefixCode
