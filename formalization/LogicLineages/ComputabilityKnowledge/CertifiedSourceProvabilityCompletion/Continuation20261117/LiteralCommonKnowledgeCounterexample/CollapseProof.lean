module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseReductionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.LogicProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.CollapseProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Derive the old selector collapse from the HB derivations of this one
tuple, then transport the literal CK code by the newly checked equivalence. -/
theorem literalCollapse : Targets.LiteralCollapse := by
  intro pF pR q c hA tag hFP h2 h3
  let d := GorbowPublishedLobReduction.delta pF c (collapseDelta tag topSelector)
  obtain ⟨hOld⟩ := CertifiedSourceProvabilityCompletion.CollapseProof.localCollapseReduction
    pF pR q c hA tag hFP topSelector
    (h2 d (.imp (prD pF c d) (collapseDelta tag topSelector)))
    (h2 (prD pF c d) (collapseDelta tag topSelector)) (h3 d)
  obtain ⟨hLiteral⟩ := ChosenCommonKnowledgeTransport.StatementChecks.exactDisplayedCommonKnowledge
    pF pR q c hA tag hFP h2 h3 topSelector
  exact SameSourceSelectorClassification.LogicProof.chain (D pF pR q c)
    (GorbowUniformCommonKnowledge.closedInstance tag topSelector literalTheta)
    (sourceC tag topSelector)
    (everyone topSelector (GorbowSortedSyntaxCode.formulaCode falseEquality))
    hLiteral hOld

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.CollapseProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCommonKnowledgeCounterexample.CollapseProof
