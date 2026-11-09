module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.Targets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof

/-- One actual S/D/CK tuple retains an installed PR computation-certificate
producer. ONE fuel precedes ALL numeral inputs and original generated codes.
The last arithmetic derivations are externally indexed CLOSED proofs, not an
object-language universal input rule, HB2/HB3, or source-collapse completion. -/
def SameRegistryProducer : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code)
    (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram pCK ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tagCK pCK ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tagCK ∧
    ProducerFor q pG ∧ RegistryInstall pF pR q tagG pG ∧
    ∃ fuel : Nat,
      (∀ sigma : Sentence, S pF pR q sigma ↔
        GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma) ∧
      ∀ inputs : List.Vector Nat 5,
        evaluate q (GorbowEnumeratedProvability.arguments c fuel 0
          (generatedFormulaCode pF q inputs) (generatedCertificate pF pG inputs)) = 1 ∧
        Nonempty (Derivation (S pF pR q) (FiniteSource.checkerEquation pF c fuel
          (generatedFormulaCode pF q inputs) (generatedCertificate pF pG inputs)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.Targets
