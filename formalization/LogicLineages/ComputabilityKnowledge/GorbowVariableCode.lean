module

public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors

@[expose] public section

/-! Source Var is a set of numeric variable codes, not every natural index.
This uses the existing term/list numbering, unchanged across ambient contexts. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowVariableCode
open GorbowCodeConstructors

def variableNumber (i : Nat) : Nat := number (variableCode i)
def decodeVariable (code : Nat) : Option Nat := do
  let raw ← GorbowNumericCertificate.decodeFormula code
  if raw.length=2 ∧ raw.getD 0 1=0 then some (raw.getD 1 0) else none
def isVariableCode (code : Nat) : Bool := (decodeVariable code).isSome
end LogicLineages.ComputabilityKnowledge.GorbowVariableCode
