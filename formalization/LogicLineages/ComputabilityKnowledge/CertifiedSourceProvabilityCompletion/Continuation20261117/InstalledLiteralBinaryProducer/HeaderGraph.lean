module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.HeaderGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem original {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (pairTag rule13Tag headerTag : Nat)
 (hp : (nodes root)[pairTag]? = some ⟨2,HistoryCodec.pair⟩)
 (h13 : (nodes root)[rule13Tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (hh : (nodes root)[headerTag]? = some ⟨2,ArithmeticTemplateEvaluation.certificateProgram CurrentNamedHeaderCertificate.template⟩)
 (r s : Term ctx) :
 Computes root CurrentNamedHeaderTransport.program (r ::ᵥ s ::ᵥ nil)
  (RetainedBaseLiteralBinary.HeaderSource.code K rule13Tag headerTag r s) := by
 let J := RuntimeOffsetAugmentationProducer.RootGraph.seedTags K pairTag rule13Tag
 have HJ : CurrentBasicProducerProgram.Installation root J := ⟨hp,H.hc,H.ha,H.hn,H.hm,h13⟩
 have HK : CurrentRecursionProducerCore.CodecBridge.Nodes root K := ⟨H.hc,H.ha,H.hn⟩
 have halias := CurrentNamedAliasCertificate.GraphProof.graph root (r ::ᵥ s ::ᵥ nil) J HJ
 have hcertificate : Computes root (ArithmeticTemplateEvaluation.certificateProgram CurrentNamedHeaderCertificate.template)
  (r ::ᵥ s ::ᵥ nil) (call headerTag (r ::ᵥ s ::ᵥ nil)) := fun tag ht =>
  GorbowPRInternalCoherence.Proof.registryCoherence arity root tag headerTag 2 _ ht hh ctx _
 have hcong := CurrentCallCongruenceProgram.UnaryGraph.closed root (r ::ᵥ s ::ᵥ nil) K H CurrentNamedHeaderTransport.unary
  CurrentNamedHeaderTransport.headerQuote CurrentNamedHeaderTransport.numberQuote
  (ArithmeticTemplateEvaluation.certificateProgram CurrentNamedHeaderCertificate.template) _ _ _
  (CurrentNamedHeaderTransport.InputGraphs.headerGraph root K HK r s)
  (CurrentNamedHeaderTransport.InputGraphs.numeralGraph root K HK r s) hcertificate
 exact CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph root (r ::ᵥ s ::ᵥ nil) K H
  CurrentNamedHeaderTransport.leftQuote CurrentNamedHeaderTransport.middleQuote CurrentNamedHeaderTransport.rightQuote
  CurrentNamedAliasCertificate.program CurrentNamedHeaderTransport.congruence _ _ _ _ _
  (CurrentNamedHeaderTransport.InputGraphs.leftGraph root K HK r s)
  (CurrentNamedHeaderTransport.CallGraphs.middleGraph root K HK r s)
  (CurrentNamedHeaderTransport.CallGraphs.rightGraph root K HK r s) halias hcong

theorem lifted {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (pairTag rule13Tag headerTag : Nat)
 (hp : (nodes root)[pairTag]? = some ⟨2,HistoryCodec.pair⟩)
 (h13 : (nodes root)[rule13Tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (hh : (nodes root)[headerTag]? = some ⟨2,ArithmeticTemplateEvaluation.certificateProgram CurrentNamedHeaderCertificate.template⟩)
 (a b c : Nat) (r s : Term ctx) :
 Computes root (.composition CurrentNamedHeaderTransport.program pairInputs) (GraphSupport.args a b c r s)
  (RetainedBaseLiteralBinary.HeaderSource.code K rule13Tag headerTag r s) :=
 GraphSupport.compose root _ _ pairInputs _ _ (GraphSupport.pair root a b c r s)
  (original root K H pairTag rule13Tag headerTag hp h13 hh r s)

theorem left {arity ctx : Nat} (root : Program arity) (K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation root K) (a b c : Nat) (r s : Term ctx) :
 Computes root (.composition CurrentNamedHeaderTransport.leftQuote pairInputs) (GraphSupport.args a b c r s)
  (FixedFormulaSubstitution.unaryValue K.ctag 5 (CurrentNamedAliasCertificate.headerCode K r s)) :=
 GraphSupport.compose root _ _ pairInputs _ _ (GraphSupport.pair root a b c r s)
  (CurrentNamedHeaderTransport.InputGraphs.leftGraph root K ⟨H.hc,H.ha,H.hn⟩ r s)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.HeaderGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.HeaderGraph
