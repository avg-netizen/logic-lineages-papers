module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.RawEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.TemplateGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof FixedFormulaSubstitution
theorem quote {arity inputs ctx : Nat} (p : Program arity) (v : List.Vector (Term ctx) inputs)
 (K : PrescribedRuntimeCallCongruence.Tags) (H : CurrentRecursionProducerCore.CodecBridge.Nodes p K)
 (t : Term inputs) :
 Computes p (LiteralTemplateQuote.templateQuote t) v
  (termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment inputs)
   (v.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) t) := by
 induction t with
 | var i =>
  simpa only [LiteralTemplateQuote.templateQuote,termValue,PrescribedRuntimeSpecialization.runtimeEnvironment,List.Vector.get_map] using
   (LiteralRawMP.ConstructorSupportProof.unary p v LiteralNumeralPrefix.numeralCode K.numeralTag H.hn _ _ (projection p v i))
 | zero =>
  have hg := binary p v HistoryCodec.cons K.ctag H.hc _ _ _ _ (constantValue p v 1) (constantValue p v 0)
  intro tag ht
  obtain ⟨he⟩ := hg tag ht
  obtain ⟨hc⟩ := FullFormulaInstantiationValidity.BoundVariableArithmeticProof.numeralCons (ctx := ctx) p K.ctag H.hc 1 []
  exact ⟨Logic.trans _ _ _ he hc⟩
 | succ t ih =>
  exact binary p v HistoryCodec.cons K.ctag H.hc _ _ _ _ (constantValue p v 2) ih
 | add t u iht ihu =>
  exact binary p v HistoryCodec.cons K.ctag H.hc _ _ _ _ (constantValue p v 3)
   (binary p v HistoryAppend.append K.atag H.ha _ _ _ _ iht ihu)
 | mul t u iht ihu =>
  exact binary p v HistoryCodec.cons K.ctag H.hc _ _ _ _ (constantValue p v 4)
   (binary p v HistoryAppend.append K.atag H.ha _ _ _ _ iht ihu)
 | universalFunction t ih =>
  exact binary p v HistoryCodec.cons K.ctag H.hc _ _ _ _ (constantValue p v 5) ih
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.TemplateGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.TemplateGraph
