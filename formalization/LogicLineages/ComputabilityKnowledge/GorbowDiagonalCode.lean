module

public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentence

@[expose] public section
/-! Uniform external code construction of the actual closed diagonal sentence.
Inputs are ambient Formula1 codes, not necessarily precisely-one-free formulas.
No internal graph, parameterized fixed point, or DCB predicate is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowDiagonalCode
open GorbowSyntax GorbowSortedSyntaxCode GorbowDiagonalSentence

def thetaRaw (raw : List Nat) : Option (List Nat) :=
  GorbowSubstitutionCode.substituteFormulaCode 1 1
    [GorbowTermPrefixCode.encode (deltaTerm (.var 0 : Term 1))] raw

def output (code : Nat) : Option Nat := do
  let raw ← decodeFormulaRaw code
  let body ← thetaRaw raw
  GorbowSortedSelfApplication.selfApply (formulaRawNumber body)
end LogicLineages.ComputabilityKnowledge.GorbowDiagonalCode
