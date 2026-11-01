module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof

def FiniteSPresentation : Prop := ∀ (pF pR : Program 1) (q : Program 5),
  Primrec (checkS pF pR q) ∧
    ∃ c : Code, GorbowEnumeratedProvability.enumeratedTheory c = S pF pR q

def ActualParameters : Prop := ∃ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c

def PublishedDiagonal : Prop := ∀ (pF pR : Program 1) (q : Program 5) (c : Code),
  GorbowSelectedDistribution.Calibrated pF pR →
  Nonempty (Derivation (S pF pR q) (GorbowBooleanTruth.biconditional
    (rho pF c) (GorbowStandardInstances.instantiate (reflectionTemplate pF c)
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))))))

def ProvabilityCalibration : Prop := ∀ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c → ∀ I formula,
  (applyProv pF c (Term.numeral formula)).realize
    (GorbowNamedRegistryInterpretation.interpretation (augmented pF q) pR I) Fin.elim0 ↔
  ∃ sigma : Sentence, formula = GorbowSortedSyntaxCode.formulaCode sigma ∧
    Nonempty (Derivation (S pF pR q) sigma)

def SProofCertification : Prop := ∀ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c → ∀ sigma : Sentence, Nonempty (Derivation (S pF pR q) sigma) →
  Nonempty (Derivation (n := 0) (S pF pR q)
    (applyProv pF c (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))))

/-- Published conditional-proof predicate, using actual closed deduction. -/
def DProofCertification : Prop := ∀ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c → ∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c) sigma) →
  Nonempty (Derivation (D pF pR q c) (prD pF c sigma))

def SelectedReflection : Prop := ∀ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c → ∀ (A : Selector) (sigma : Sentence),
  Nonempty (Derivation (D pF pR q c)
    (.imp (prD pF c sigma) (everyone A
      (GorbowSortedSyntaxCode.formulaCode sigma))))

def SelectedDistribution : Prop := ∀ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c → ∀ (A : Selector) (sigma tau : Sentence),
  Nonempty (Derivation (D pF pR q c)
    (GorbowSelectedDistribution.selectedDistribution A sigma tau))

/-- All three source-shaped clauses in ONE explicit actual parameter choice,
with the published diagonal sentence and the genuine proof predicate above. -/
def CompleteThree : Prop := ∃ (pF pR : Program 1) (q : Program 5) (c : Code),
  Actual pF pR q c ∧ ∀ (A : Selector) (sigma tau : Sentence),
    (Nonempty (Derivation (D pF pR q c) sigma) →
      Nonempty (Derivation (D pF pR q c) (everyone A
        (GorbowSortedSyntaxCode.formulaCode sigma)))) ∧
    Nonempty (Derivation (D pF pR q c)
      (GorbowSelectedDistribution.selectedDistribution A sigma tau)) ∧
    Nonempty (Derivation (D pF pR q c)
      (.imp (prD pF c sigma) (everyone A
        (GorbowSortedSyntaxCode.formulaCode sigma))))

def Target : Prop := FiniteSPresentation ∧ ActualParameters ∧ PublishedDiagonal ∧
  ProvabilityCalibration ∧ SProofCertification ∧ DProofCertification ∧
  SelectedReflection ∧ SelectedDistribution ∧ CompleteThree

end LogicLineages.ComputabilityKnowledge.GorbowPublishedDCB.Targets
