module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.TemplateProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.EncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.RawEncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution
theorem rawValue {n k ctx : Nat} (p : Program n) (J : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentRecursionProducerCore.CodecBridge.Nodes p J)
 (t : Term k) (ht : ArithmeticTemplateEvaluation.Arithmetic t) (v : List.Vector (Term ctx) k) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (ArithmeticTemplateEvaluation.SymbolicProof.raw J.numeralTag J.ctag J.atag v t)
  (termValue J.ctag J.atag (PrescribedRuntimeSpecialization.runtimeEnvironment k)
   (v.map (LiteralNumeralPrefix.numeralCall J.numeralTag)) t))) := by
 induction t with
 | var i =>
  simpa only [ArithmeticTemplateEvaluation.SymbolicProof.raw,termValue,
   PrescribedRuntimeSpecialization.runtimeEnvironment,List.Vector.get_map] using
   (show Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (LiteralNumeralPrefix.numeralCall J.numeralTag (v.get i))
     (LiteralNumeralPrefix.numeralCall J.numeralTag (v.get i)))) from ⟨.logical (.reflexive _)⟩)
 | zero =>
  exact BoundVariableArithmeticProof.numeralCons p J.ctag H.hc 1 []
 | succ t ih =>
  obtain ⟨h⟩ := ih ht
  exact CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 2 H.hc H.hc _ _ h
 | add t u iht ihu =>
  obtain ⟨ht'⟩ := iht ht.1
  obtain ⟨hu'⟩ := ihu ht.2
  exact CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 3 H.hc H.ha H.hc H.ha _ _ _ _ ht' hu'
 | mul t u iht ihu =>
  obtain ⟨ht'⟩ := iht ht.1
  obtain ⟨hu'⟩ := ihu ht.2
  exact CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 4 H.hc H.ha H.hc H.ha _ _ _ _ ht' hu'
 | universalFunction t ih => exact False.elim ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.RawEncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.RawEncodingProof
