module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.TemplateGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.InputGraphs
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof FixedFormulaSubstitution
theorem headerEncoding {arity ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (r s : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
   ((r ::ᵥ s ::ᵥ nil).map (LiteralNumeralPrefix.numeralCall K.numeralTag)) header)
   (CurrentNamedAliasCertificate.headerCode K r s))) := by
 obtain ⟨hh⟩ := CurrentNamedAliasCertificate.EncodingProof.header p K H
  (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
  ((r ::ᵥ s ::ᵥ nil).map (LiteralNumeralPrefix.numeralCall K.numeralTag)) 0 (argumentVariables 2)
 rw [CurrentCompositionCertificate.RootEncodingProof.argumentValues] at hh
 simpa only [header,CurrentNamedHeaderCertificate.template,GorbowNamedDefiningTheory.headerVariables,
  CurrentNamedAliasCertificate.headerCode,List.Vector.map_cons,List.Vector.map_nil,Term.numeral] using (show Nonempty _ from ⟨hh⟩)

theorem headerGraph {arity ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (r s : Term ctx) : Computes p headerQuote (r ::ᵥ s ::ᵥ nil) (CurrentNamedAliasCertificate.headerCode K r s) := by
 intro tag ht
 obtain ⟨hg⟩ := TemplateGraph.quote p (r ::ᵥ s ::ᵥ nil) K H header tag ht
 obtain ⟨he⟩ := headerEncoding p K H r s
 exact ⟨Logic.trans _ _ _ hg he⟩

theorem valueGraph {arity ctx : Nat} (p : Program arity) (r s : Term ctx) :
 Computes p value (r ::ᵥ s ::ᵥ nil) (GorbowRegistryTuple.headerTerm 2 0 [r,s]) := by
 intro tag ht
 obtain ⟨hv⟩ := ArithmeticTemplateEvaluation.ValueProof.computes header CurrentNamedHeaderCertificate.TemplateProof.arithmetic p (r ::ᵥ s ::ᵥ nil) tag ht
 have hv' := hv.finish
 rw [CurrentNamedHeaderCertificate.TemplateProof.value] at hv'
 exact ⟨hv'⟩

theorem numeralGraph {arity ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (r s : Term ctx) : Computes p numberQuote (r ::ᵥ s ::ᵥ nil)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s])) :=
 LiteralRawMP.ConstructorSupportProof.unary p (r ::ᵥ s ::ᵥ nil) LiteralNumeralPrefix.numeralCode K.numeralTag H.hn _ _ (valueGraph p r s)

theorem leftGraph {arity ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (r s : Term ctx) : Computes p leftQuote (r ::ᵥ s ::ᵥ nil)
  (unaryValue K.ctag 5 (CurrentNamedAliasCertificate.headerCode K r s)) :=
 binary p (r ::ᵥ s ::ᵥ nil) HistoryCodec.cons K.ctag H.hc _ _ _ _
  (constantValue p (r ::ᵥ s ::ᵥ nil) 5) (headerGraph p K H r s)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.InputGraphs
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.InputGraphs
