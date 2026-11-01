module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker

@[expose] public section
/-! The literal universally coded source K2 axiom over the concrete finite
named PR defining theory. Sentence guards and implication codes must be
derived from that theory; no collection of literal distribution instances
is added as a replacement. This is not a self-indexed DCB presentation. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution
open GorbowSyntax GorbowPRProgram List.Vector

def Calibrated (pF pR : Program 1) : Prop :=
  (∀ x, evaluate pF (x ::ᵥ List.Vector.nil) = GorbowSourceRegistryPadding.sourceFunction x) ∧
  (∀ x, evaluate pR (x ::ᵥ List.Vector.nil) = GorbowSourceRegistryPadding.sourceRelationValue x)

def Theory (pF pR : Program 1) : Sentence → Prop := fun sigma =>
  GorbowNamedDefiningTheory.Theory pF pR sigma ∨
    sigma = GorbowSortedKnowledgeAxioms.distribution

def check (pF pR : Program 1) (raw : List Nat) : Bool :=
  GorbowNamedDefiningTheory.check pF pR raw ||
    decide (raw = GorbowFormulaPrefixCode.encode GorbowSortedKnowledgeAxioms.distribution)

def sentenceGuard (sigma : Sentence) : Sentence :=
  GorbowBooleanTruth.sentenceGuard (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))

def implicationCode (sigma tau : Sentence) : Sentence :=
  .equal (GorbowBooleanTruth.binaryCodeTerm 0
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode tau)))
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode (.imp sigma tau)))

def selectedDistribution (A : Selector) (sigma tau : Sentence) : Sentence :=
  .imp (everyone A (GorbowSortedSyntaxCode.formulaCode (.imp sigma tau)))
    (.imp (everyone A (GorbowSortedSyntaxCode.formulaCode sigma))
      (everyone A (GorbowSortedSyntaxCode.formulaCode tau)))

end LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution
