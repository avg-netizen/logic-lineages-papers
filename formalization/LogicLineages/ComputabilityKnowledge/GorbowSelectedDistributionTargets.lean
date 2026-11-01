module

public import LogicLineages.ComputabilityKnowledge.GorbowSelectedDistributionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof

def ActualPrograms : Prop := ∃ pF pR : Program 1, Calibrated pF pR

def NumericAxiomChecker : Prop := ∀ pF pR : Program 1,
  Primrec (check pF pR) ∧
    GorbowTheoryChecker.ProgramTheory (check pF pR) = Theory pF pR

def LiteralCodingCertificates : Prop := ∀ pF pR : Program 1, Calibrated pF pR →
  (∀ sigma : Sentence, Nonempty (Derivation (Theory pF pR) (sentenceGuard sigma))) ∧
  (∀ sigma tau : Sentence, Nonempty (Derivation (Theory pF pR) (implicationCode sigma tau)))

def SelectedAgentClosure : Prop := ∀ pF pR : Program 1, Calibrated pF pR →
  ∀ (A : Selector) (sigma tau : Sentence),
    Nonempty (Derivation (Theory pF pR) (selectedDistribution A sigma tau))

def CompleteSupplier : Prop := ∃ pF pR : Program 1,
  Calibrated pF pR ∧ Primrec (check pF pR) ∧
    GorbowTheoryChecker.ProgramTheory (check pF pR) = Theory pF pR ∧
      ∀ (A : Selector) (sigma tau : Sentence),
        Nonempty (Derivation (Theory pF pR) (selectedDistribution A sigma tau))

def Target : Prop := ActualPrograms ∧ NumericAxiomChecker ∧
  LiteralCodingCertificates ∧ SelectedAgentClosure ∧ CompleteSupplier

end LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution.Targets
