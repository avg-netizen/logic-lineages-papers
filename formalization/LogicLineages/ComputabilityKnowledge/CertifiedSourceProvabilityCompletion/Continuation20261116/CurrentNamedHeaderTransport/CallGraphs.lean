module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.InputGraphs
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.CallGraphs
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof FixedFormulaSubstitution
theorem callEncoding {arity inputs ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (v : List.Vector (Term ctx) inputs) (t : Term inputs) (raw : Term ctx)
 (he : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment inputs)
   (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) t) raw)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment inputs)
   (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) (call GorbowSourceRegistryPadding.functionTag (t ::ᵥ nil)))
   (PrescribedRuntimeCallCongruence.callValue K (Term.numeral GorbowSourceRegistryPadding.functionTag) (raw ::ᵥ nil)))) := by
 obtain ⟨hc⟩ := CurrentCompositionCertificate.CallEncodingProof.call p K H.hc H.ha H.hn
  (PrescribedRuntimeSpecialization.runtimeEnvironment inputs)
  (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) GorbowSourceRegistryPadding.functionTag (t ::ᵥ nil)
 obtain ⟨he'⟩ := CurrentRecursionProducerCore.CallRawCopy.call p K K H H
  (Term.numeral GorbowSourceRegistryPadding.functionTag)
  ((t ::ᵥ nil).map (termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment inputs)
   (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)))) (raw ::ᵥ nil) (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact he)
 exact ⟨Logic.trans _ _ _ hc he'⟩

theorem middleGraph {arity ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (r s : Term ctx) : Computes p middleQuote (r ::ᵥ s ::ᵥ nil)
  (PrescribedRuntimeCallCongruence.callValue K (Term.numeral GorbowSourceRegistryPadding.functionTag)
   (CurrentNamedAliasCertificate.headerCode K r s ::ᵥ nil)) := by
 intro tag ht
 obtain ⟨hg⟩ := TemplateGraph.quote p (r ::ᵥ s ::ᵥ nil) K H
  (call GorbowSourceRegistryPadding.functionTag (header ::ᵥ nil)) tag ht
 obtain ⟨he⟩ := InputGraphs.headerEncoding p K H r s
 obtain ⟨hc⟩ := callEncoding p K H (r ::ᵥ s ::ᵥ nil) header _ he
 exact ⟨Logic.trans _ _ _ hg hc⟩

theorem rightGraph {arity ctx : Nat} (p : Program arity)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (r s : Term ctx) : Computes p rightQuote (r ::ᵥ s ::ᵥ nil)
  (PrescribedRuntimeCallCongruence.callValue K (Term.numeral GorbowSourceRegistryPadding.functionTag)
   (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowRegistryTuple.headerTerm 2 0 [r,s]) ::ᵥ nil)) := by
 intro tag ht
 let hv := GorbowRegistryTuple.headerTerm 2 0 [r,s]
 obtain ⟨he⟩ := Equations.compositionValues p tag (LiteralTemplateQuote.templateQuote unary) (fun _ => value) ht
  (r ::ᵥ s ::ᵥ nil) (hv ::ᵥ nil) (fun i => by
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact InputGraphs.valueGraph p r s _ (Equations.argumentChild p tag _ _ ht 0))
 obtain ⟨hq⟩ := TemplateGraph.quote p (hv ::ᵥ nil) K H unary (tag+1) (Equations.functionChild p tag _ _ ht)
 obtain ⟨hc⟩ := callEncoding p K H (hv ::ᵥ nil) (.var 0) (LiteralNumeralPrefix.numeralCall K.numeralTag hv)
  (.logical (.reflexive _))
 exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ hq hc)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.CallGraphs
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.CallGraphs
