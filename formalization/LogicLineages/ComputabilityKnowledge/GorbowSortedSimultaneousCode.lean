module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCode
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode

@[expose] public section
/-! Literal sorted simultaneous closed-term substitution, with an explicit
ambient context and exact full-language closed-term dictionary domain.
This is not an atomic truth axiom or a represented substitution graph. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCode
open GorbowSortedSyntaxCode

def dictionaryRaw (codes : List Nat) : List (List Nat) :=
  codes.map (fun code => (decodeTermRaw code).getD [])

def dictionaryOK (n : Nat) (codes : List Nat) : Bool :=
  decide (codes.length=n) && codes.all GorbowSortedBooleanCode.fullTermCode

def substituteNumber (n code : Nat) (codes : List Nat) : Option Nat := do
  let raw ← decodeFormulaRaw code
  if dictionaryOK n codes then
    (GorbowSubstitutionCode.substituteFormulaCode n 0 (dictionaryRaw codes) raw).map formulaRawNumber
  else none
end LogicLineages.ComputabilityKnowledge.GorbowSortedSimultaneousCode
