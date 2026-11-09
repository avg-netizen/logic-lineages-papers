module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.TagTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry

/-- The AST being evaluated is fixed before the PR generator. Its occurrence
tag is a RUNTIME input, and the ambient registry is quantified afterward.
This permits installation of the generator without specializing certificates
to obsolete tags. It is not a uniform PR evaluator of arbitrary ASTs. -/
def TagParametricCertificates : Prop :=
  ∀ m (q : Program m),
    ∃ produce : Nat × List.Vector Nat m → Nat,
      Primrec produce ∧
      ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨m, q⟩ →
      ∀ inputs : List.Vector Nat m,
      GorbowTheoryNumericCertificate.check (registryAxiomCheck p) 0
        (GorbowSortedSyntaxCode.formulaCode (calculation tag q inputs))
        (produce (tag, inputs)) = true

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.TagTargets
