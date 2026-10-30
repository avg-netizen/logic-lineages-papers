module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumericCode
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCode
public import LogicLineages.ComputabilityKnowledge.GorbowClosedTermCode

@[expose] public section

/-! Literal numeric instances for an arbitrary unique free variable INDEX.
The separate variable-code decoder supplies the source Var domain later.
The term domain here is full closed L, not merely arithmetic terms. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCode
open GorbowCodeConstructors GorbowRawContextBound GorbowNamedBindingCode

def instanceNumber (v formulaCode termCode : Nat) : Option Nat := do
  let raw ← GorbowNamedNumericCode.namedInput v formulaCode
  let selected ← selectCode (rawBound raw) v raw
  let traw ← GorbowNumericCertificate.decodeFormula termCode
  let out ← GorbowInstanceCode.instanceCode 0 selected traw
  pure (number out)
end LogicLineages.ComputabilityKnowledge.GorbowNamedInstanceCode
