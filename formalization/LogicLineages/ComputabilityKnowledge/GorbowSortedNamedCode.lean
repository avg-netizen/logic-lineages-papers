module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCode

@[expose] public section

/-! Sorted source-varCode codes are decoded before index-level algorithms.
All formula results are retagged. These are literal syntax/code translations,
not a correspondence between tagged and legacy semantic revision sequences. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCode
open GorbowSortedSyntaxCode

def decodeInputs (varCode formula : Nat) : Option (Nat × Nat) := do
  let i ← decodeVariable varCode
  if formula%2=0 then some (i,formula/2) else none

def namedFormula (varCode formula : Nat) : Bool :=
  (do let p ← decodeInputs varCode formula; GorbowNamedNumericCode.namedInput p.1 p.2).isSome

def allNumber (varCode formula : Nat) : Option Nat := do
  let p ← decodeInputs varCode formula
  (GorbowNamedNumericCode.allNumber p.1 p.2).map tagFormula
def exNumber (varCode formula : Nat) : Option Nat := do
  let p ← decodeInputs varCode formula
  (GorbowNamedNumericCode.exNumber p.1 p.2).map tagFormula
def instanceNumber (varCode formula term : Nat) : Option Nat := do
  let p ← decodeInputs varCode formula
  if term%2=1 then (GorbowNamedInstanceCode.instanceNumber p.1 p.2 (term/2)).map tagFormula else none
end LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCode
