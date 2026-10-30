module

public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCode
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! Syntactic self-application only, NOT the diagonal fixed-point lemma or
arithmetical representability. Ambient unary formulas need not use their
variable; the separate Selector guard enforces actual occurrence. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSelfApplicationCode
open GorbowSyntax

def selfInstance (φ : Formula 1) : Sentence :=
  GorbowStandardInstances.instantiate φ (Term.numeral (GorbowCodeConstructors.formulaNumber φ))

def selfApplicationCode (raw : List Nat) : Option (List Nat) :=
  GorbowSubstitutionCode.substituteFormulaCode 1 0
    [GorbowCodeConstructors.numeral (GorbowCodeConstructors.number raw)] raw

def selectorSelfApplicationCode (raw : List Nat) : Option (List Nat) :=
  if GorbowSupportCode.selectorCode raw then selfApplicationCode raw else none
end LogicLineages.ComputabilityKnowledge.GorbowSelfApplicationCode
