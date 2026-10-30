module

public import LogicLineages.ComputabilityKnowledge.GorbowRawContextBound
public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCode
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate

@[expose] public section

/-! Numeric arbitrary-free-name binding with a proved conservative parser
ambient and exact singleton support guard. No source [t/v] code operation or
uniformly coded quantifier truth axiom is asserted by this module. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCode
open GorbowRawContextBound GorbowNamedBindingCode GorbowCodeConstructors

def namedInput (v code : Nat) : Option (List Nat) := do
  let raw ← GorbowNumericCertificate.decodeFormula code
  if v<rawBound raw ∧ GorbowSupportCode.formulaNames (rawBound raw) raw=some [v] then some raw else none

def bindNumber (tag v code : Nat) : Option Nat := do
  let raw ← namedInput v code
  let out ← bindCode tag (rawBound raw) v raw
  pure (number out)
def allNumber (v code : Nat) : Option Nat := bindNumber 10 v code
def exNumber (v code : Nat) : Option Nat := bindNumber 11 v code

def selectNumber (v code : Nat) : Option Nat := do
  let raw ← namedInput v code
  let out ← selectCode (rawBound raw) v raw
  pure (number out)
end LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCode
