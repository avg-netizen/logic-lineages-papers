module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.ImplicationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.LiteralBridgeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Each direction uses its genuine ordinary theorem and its own literal
Gödel code. The chosen constructor and source tuple stay fixed throughout. -/
theorem displayedCommonKnowledge : Targets.DisplayedCommonKnowledge := by
  intro pF pR q c hA tag hFP h2 h3 A
  obtain ⟨hForward⟩ := ImplicationProof.implicationTransport pF pR q c hA tag hFP h2 h3
    A literalTheta sourceTheta (LiteralBridgeProof.displayedThetaReverse (D pF pR q c))
  obtain ⟨hReverse⟩ := ImplicationProof.implicationTransport pF pR q c hA tag hFP h2 h3
    A sourceTheta literalTheta (LiteralProof.displayedThetaBridge (D pF pR q c))
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hForward) hReverse⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Proof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Proof
