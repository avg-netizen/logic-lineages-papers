module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.CallGraphs
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.UnaryGraph
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TransitivityGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof FixedFormulaSubstitution
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

def result {ctx : Nat} (K : Tags) (aliasTag certificateTag : Nat) (r s : Term ctx) : Term ctx :=
 let h := CurrentNamedAliasCertificate.headerCode K r s
 let v := LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])
 let f := callValue K (Term.numeral GorbowSourceRegistryPadding.functionTag)
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (unaryValue K.ctag 5 h) (f (h ::ᵥ nil)) (f (v ::ᵥ nil))
  (call aliasTag (r ::ᵥ s ::ᵥ nil))
  (PrescribedRuntimeCallCongruence.unaryCertificate K unary h v (call certificateTag (r ::ᵥ s ::ᵥ nil)))

theorem graph {arity ctx : Nat} (p : Program arity) (K : Tags)
 (H : CurrentCallCongruenceProgram.Installation p K) (aliasTag certificateTag : Nat)
 (ha : (nodes p)[aliasTag]? = some ⟨2,CurrentNamedAliasCertificate.program⟩)
 (hc : (nodes p)[certificateTag]? = some ⟨2,ArithmeticTemplateEvaluation.certificateProgram header⟩)
 (r s : Term ctx) : Computes p program (r ::ᵥ s ::ᵥ nil) (result K aliasTag certificateTag r s) := by
 let v := r ::ᵥ s ::ᵥ nil
 have HK : CurrentRecursionProducerCore.CodecBridge.Nodes p K := ⟨H.hc,H.ha,H.hn⟩
 have halias : Computes p CurrentNamedAliasCertificate.program v (call aliasTag v) := fun tag ht =>
  GorbowPRInternalCoherence.Proof.registryCoherence arity p tag aliasTag 2 _ ht ha ctx v
 have hcertificate : Computes p (ArithmeticTemplateEvaluation.certificateProgram header) v (call certificateTag v) := fun tag ht =>
  GorbowPRInternalCoherence.Proof.registryCoherence arity p tag certificateTag 2 _ ht hc ctx v
 have hcong := CurrentCallCongruenceProgram.UnaryGraph.closed p v K H unary headerQuote numberQuote
  (ArithmeticTemplateEvaluation.certificateProgram header) _ _ _
  (InputGraphs.headerGraph p K HK r s) (InputGraphs.numeralGraph p K HK r s) hcertificate
 exact CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph p v K H
  leftQuote middleQuote rightQuote CurrentNamedAliasCertificate.program congruence _ _ _ _ _
  (InputGraphs.leftGraph p K HK r s) (CallGraphs.middleGraph p K HK r s)
  (CallGraphs.rightGraph p K HK r s) halias hcong
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.GraphProof
