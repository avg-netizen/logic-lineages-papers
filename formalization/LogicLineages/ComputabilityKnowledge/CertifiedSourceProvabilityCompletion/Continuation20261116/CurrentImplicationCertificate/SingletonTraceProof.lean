module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.SingletonTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem nativeLine (isS : Bool) (A B C : Formula 0) :
 UniformClosedPropositional.nativeLine isS (GorbowFormulaPrefixCode.encode A)
  (GorbowFormulaPrefixCode.encode B) (GorbowFormulaPrefixCode.encode C) =
 GorbowProofChecker.logicalLine (if isS then .s A B C else .k A B) := by
 cases isS <;> rfl

theorem line {arity ctx : Nat} (p : Program arity) (tag : Nat) (isS : Bool)
 (ht : (nodes p)[tag]? = some ⟨3,UniformClosedPropositional.lineConstructor isS⟩)
 (A B C : Formula 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedPropositional.lineCall tag
   (formulaNumeral (ctx := ctx) A) (formulaNumeral B) (formulaNumeral C))
   (Term.numeral (Encodable.encode (GorbowProofChecker.logicalLine (if isS then .s A B C else .k A B)))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag (UniformClosedPropositional.lineConstructor isS) ht
  (Encodable.encode (GorbowFormulaPrefixCode.encode A) ::ᵥ Encodable.encode (GorbowFormulaPrefixCode.encode B) ::ᵥ
   Encodable.encode (GorbowFormulaPrefixCode.encode C) ::ᵥ nil) ctx
 rw [UniformClosedPropositional.StatementChecks.exactNativeLine,nativeLine] at h
 simpa only [UniformClosedPropositional.lineCall,formulaNumeral,List.Vector.map_cons,List.Vector.map_nil] using (show Nonempty _ from ⟨h⟩)

theorem singleton {arity ctx : Nat} (p : Program arity) (ctag tag : Nat) (isS : Bool)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨3,UniformClosedPropositional.lineConstructor isS⟩)
 (A B C : Formula 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedPropositionalCertificate.certificate ctag tag
   (formulaNumeral (ctx := ctx) A) (formulaNumeral B) (formulaNumeral C))
   (Term.numeral (UniformClosedPropositional.singletonNumber isS A B C)))) := by
 obtain ⟨hl⟩ := line p tag isS ht A B C (ctx := ctx)
 have he := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hc⟩ := PrescribedRuntimeSpecialization.PrimitiveProof.consNumeral p ctag hc
  (GorbowProofChecker.logicalLine (if isS then .s A B C else .k A B)) (ctx := ctx)
 exact ⟨Logic.trans _ _ _ he hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.SingletonTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.SingletonTraceProof
