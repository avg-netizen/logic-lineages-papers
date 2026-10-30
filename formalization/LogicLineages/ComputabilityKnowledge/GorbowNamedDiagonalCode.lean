module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalCode
public import LogicLineages.ComputabilityKnowledge.GorbowSortedNamedCode

@[expose] public section
/-! Original-name closed diagonal code construction. The domain is an actual
sorted variable code and a formula with precisely that singleton free support.
Selection changes syntax explicitly; no source-code identity is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalCode

def select (varCode formula : Nat) : Option Nat :=
  if GorbowSortedNamedCode.namedFormula varCode formula then do
    let p ← GorbowSortedNamedCode.decodeInputs varCode formula
    let code ← GorbowNamedNumericCode.selectNumber p.1 p.2
    pure (GorbowSortedSyntaxCode.tagFormula code)
  else none

def output (varCode formula : Nat) : Option Nat :=
  (select varCode formula).bind GorbowDiagonalCode.output
end LogicLineages.ComputabilityKnowledge.GorbowNamedDiagonalCode
