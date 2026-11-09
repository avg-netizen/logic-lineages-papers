module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSource
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB

/-- Literal closed source-verifier call, at its original installed tag and
input order. This is a numeral equation, not an internal universal checker
preservation axiom. -/
def checkerEquation (pF : Program 1) (c : Code) (fuel formula certificate : Nat) : Sentence :=
  .equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
    (GorbowPRNumeralCalculation.numeralArguments
      (GorbowEnumeratedProvability.arguments c fuel 0 formula certificate))) (Term.numeral 1)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSource
