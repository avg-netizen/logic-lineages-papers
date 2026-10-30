module

public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCode
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode

@[expose] public section
/-! Literal syntactic self-application with the globally sorted formula code.
This stage is not yet a logical fixed point. Ambient Formula1 inputs need not
have precisely one free variable; exact source support is a separate guard. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplication
open GorbowSyntax GorbowSortedSyntaxCode

def selfInstance (φ : Formula 1) : Sentence :=
  GorbowStandardInstances.instantiate φ (Term.numeral (formulaCode φ))

def rawSelf (raw : List Nat) : Option (List Nat) :=
  GorbowInstanceCode.instanceCode 0 raw (GorbowCodeConstructors.numeral (formulaRawNumber raw))

def selfApply (code : Nat) : Option Nat := do
  let raw ← decodeFormulaRaw code
  let out ← rawSelf raw
  pure (formulaRawNumber out)
end LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplication
