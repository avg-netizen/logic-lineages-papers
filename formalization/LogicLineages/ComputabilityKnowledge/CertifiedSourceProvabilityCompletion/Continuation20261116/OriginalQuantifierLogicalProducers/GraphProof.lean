module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.LineGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem exactInternal : Targets.Internal := by
 intro arity p isExists ptag ctag atag lineTag singletonTag I hline hsingle ctx a b
 let values := a ::ᵥ b ::ᵥ nil
 have hcomputed := LineGraph.lineAt p [] ptag ctag atag I.hp I.hc I.ha isExists
  (.projection 0) (.projection 1) values a b (projection p [] values 0) (projection p [] values 1)
 obtain ⟨hl⟩ := hcomputed lineTag hline
 have hsingleton := binary p [] values HistoryCodec.cons _ _ _ _ _
  (copies p [] _ lineTag hline values) (constantValue p [] values 0) (copies p [] _ ctag I.hc _)
 obtain ⟨hs⟩ := hsingleton singletonTag hsingle
 exact ⟨⟨Hilbert.Local.finish hl⟩,⟨Hilbert.Local.finish hs⟩⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.GraphProof
