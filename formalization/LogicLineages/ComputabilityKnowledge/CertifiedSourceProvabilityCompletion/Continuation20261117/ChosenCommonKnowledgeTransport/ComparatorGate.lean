module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Targets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ComparatorGate
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

theorem implicationTransport : Targets.ImplicationTransport ↔ (
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  ∀ (A : Selector) (sigma tau : Sentence),
    Nonempty (Derivation (D pF pR q c) (.imp sigma tau)) →
    Nonempty (Derivation (D pF pR q c)
      (.imp (GorbowUniformCommonKnowledge.closedInstance tag A sigma)
        (GorbowUniformCommonKnowledge.closedInstance tag A tau)))) := Iff.rfl

theorem displayedThetaReverse : Targets.DisplayedThetaReverse ↔ (
  ∀ T : Sentence → Prop, Nonempty (Derivation T
    (.imp
      (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality)
      (.imp (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality))
        falseEquality)))) := Iff.rfl

theorem displayedCommonKnowledge : Targets.DisplayedCommonKnowledge ↔ (
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
    (GorbowBooleanTruth.biconditional
      (GorbowUniformCommonKnowledge.closedInstance tag A
        (.imp (GorbowSortedRevisionEventual.allAgentsKnow falseEquality) falseEquality))
      (GorbowUniformCommonKnowledge.closedInstance tag A
        (.imp (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality))
          falseEquality))))) := Iff.rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ComparatorGate

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ComparatorGate
