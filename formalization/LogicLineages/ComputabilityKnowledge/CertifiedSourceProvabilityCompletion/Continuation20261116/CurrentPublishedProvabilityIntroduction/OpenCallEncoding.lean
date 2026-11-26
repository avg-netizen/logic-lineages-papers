module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CallEncodingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OpenCallEncoding
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence GorbowRegistryTuple
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentCompositionCertificate.CallEncodingProof

theorem call {arity n depth inputs ctx m : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (tagTerm : Term n) (tag : Term ctx)
 (args : List.Vector (Term n) m)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw tagTerm) (LiteralNumeralPrefix.numeralCall J.numeralTag tag))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw (CurrentRecursionBaseProgram.openCall tagTerm args))
   (callValue J tag (args.map (termValue J.ctag J.atag e raw))))) := by
 obtain ⟨hArity⟩ := numeral p J.ctag J.atag hc e raw m
 obtain ⟨hp⟩ := pairCongruence p J hc ha _ _ _ _ ht
  (.logical (.reflexive (tupleValue J (args.toList.map (termValue J.ctag J.atag e raw)))))
 obtain ⟨hh⟩ := pairCongruence p J hc ha _ _ _ _ hArity hp
 obtain ⟨hu⟩ := CurrentCompositionCertificate.CodecProof.unary p J.ctag J.ctag 5 hc hc _ _ hh
 simpa only [CurrentRecursionBaseProgram.openCall,termValue,pairMap,tupleMap,
  callValue,headerValue,List.Vector.toList_map] using (show Nonempty _ from ⟨hu⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OpenCallEncoding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OpenCallEncoding
