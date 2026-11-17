module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Targets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.ComparatorGate
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

theorem literalCollapse : Targets.LiteralCollapse ↔ (
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  Nonempty (Derivation (D pF pR q c)
    (GorbowBooleanTruth.biconditional
      (GorbowUniformCommonKnowledge.closedInstance tag topSelector
        (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality))
      (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality))))) := Iff.rfl

theorem literalCounterexample : Targets.LiteralCounterexample ↔ (
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  Nonempty (GorbowPublishedKT.Proof false pF pR q c
    (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)) ∧
  Nonempty (GorbowPublishedKT.Proof false pF pR q c
    (.neg (GorbowUniformCommonKnowledge.closedInstance tag topSelector
      (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)))) ∧
  (∀ r : Nat, Nonempty (GorbowPublishedKT.Proof false pF pR q c
    (selectedIteration topSelector r
      (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)))) ∧
  ¬ Nonempty (GorbowPublishedKT.Proof false pF pR q c
    (GorbowUniformCommonKnowledge.closedInstance tag topSelector
      (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)))) := Iff.rfl

theorem fromSelectedPresentation : Targets.FromSelectedPresentation ↔ (
  SourceBaseCompletion.SelectedVerifierTargets.SelectedCertifiedPresentation →
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
        (GorbowUniformCommonKnowledge.closedInstance tag topSelector
          (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality))
        (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality)))) ∧
    Nonempty (GorbowPublishedKT.Proof false pF pR q c
      (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)) ∧
    Nonempty (GorbowPublishedKT.Proof false pF pR q c
      (.neg (GorbowUniformCommonKnowledge.closedInstance tag topSelector
        (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)))) ∧
    (∀ r : Nat, Nonempty (GorbowPublishedKT.Proof false pF pR q c
      (selectedIteration topSelector r
        (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)))) ∧
    ¬ Nonempty (GorbowPublishedKT.Proof false pF pR q c
      (GorbowUniformCommonKnowledge.closedInstance tag topSelector
        (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)))) := Iff.rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.ComparatorGate

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.ComparatorGate
