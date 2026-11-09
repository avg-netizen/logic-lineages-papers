module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate

@[expose] public section
/-! Effective numerical certificates for each FIXED finite PR program.
The original sorted formula and List Line certificate encodings are retained.
No uniform primitive-recursive evaluator over all program ASTs is requested.
The external generator is a prerequisite, not internal checker preservation. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations

/-- Literal finite membership in the original registry node equations. -/
def registryAxiomCheck {n : Nat} (p : Program n) (raw : List Nat) : Bool :=
  decide (raw ∈ (axioms p).map GorbowFormulaPrefixCode.encode)

/-- The exact original numerical equation proved by numeralCalculation. -/
def calculation {m : Nat} (tag : Nat) (q : Program m)
    (inputs : List.Vector Nat m) : Sentence :=
  .equal (call tag (GorbowPRNumeralCalculation.numeralArguments inputs))
    (Term.numeral (evaluate q inputs))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral
