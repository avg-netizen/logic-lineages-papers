module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseDefinitions
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.SelectedVerifierTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- The displayed literal sentence has its own chosen-CK code. Internal HB
remains explicit at this SAME original tuple; no source is reselected. -/
def LiteralCollapse : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  Nonempty (Derivation (D pF pR q c)
    (GorbowBooleanTruth.biconditional
      (GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta)
      (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality))))

/-- Literal eq:counterexample and its finite-iteration/nonprovability
consequences. Both original theories retain the actual
closedInstance of literalTheta and one source tuple; the optional UBF flag
does not change the literal formula or its code. -/
def LiteralFacts (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) : Prop :=
  ∀ withUBF : Bool,
  Nonempty (GorbowPublishedKT.Proof withUBF pF pR q c literalTheta) ∧
  Nonempty (GorbowPublishedKT.Proof withUBF pF pR q c
    (.neg (GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta))) ∧
  (∀ r : Nat, Nonempty (GorbowPublishedKT.Proof withUBF pF pR q c
    (selectedIteration topSelector r literalTheta))) ∧
  ¬ Nonempty (GorbowPublishedKT.Proof withUBF pF pR q c
    (GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta))

/-- The complete literal conclusion at every original certified tuple.
Consistency is derived from Actual, never added as a new premise. -/
def LiteralCounterexample : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  LiteralFacts pF pR q c tag

/-- The original selected certified presentation, retaining all of its
fields at one witness tuple, extended by the exact literal conclusions. -/
def SourceCounterexample : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb2 pF c sigma tau))) ∧
    (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb3 pF c sigma))) ∧
    Nonempty (Derivation (D pF pR q c)
      (GorbowBooleanTruth.biconditional
        (GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta)
        (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality)))) ∧
    LiteralFacts pF pR q c tag

/-- A lightweight consumer of the unchanged selected-presentation contract.
Its antecedent remains explicit; this theorem alone does not revalidate the
large source-installation witness or prove SourceCounterexample outright. -/
def FromSelectedPresentation : Prop :=
  SourceBaseCompletion.SelectedVerifierTargets.SelectedCertifiedPresentation →
    SourceCounterexample

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Targets
