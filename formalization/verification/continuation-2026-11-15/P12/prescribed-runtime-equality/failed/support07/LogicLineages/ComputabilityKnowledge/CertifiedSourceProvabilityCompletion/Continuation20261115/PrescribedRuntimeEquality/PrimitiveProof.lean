module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.PrimitiveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem nativeReplacement (f : Formula 1) (t u : Term 0) :
 UniformClosedRule12.nativeLine (GorbowFormulaPrefixCode.encode f)
  (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) =
 GorbowProofChecker.logicalLine (.equalityReplace f t u) := by
 have h : GorbowLogicalAxiomCode.case12 0
  [GorbowFormulaPrefixCode.encode f,GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u] =
  some (GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.equalityReplace f t u))) :=
  (GorbowLogicalAxiomCodeProof.exactCompilation 0 _ _).mpr ⟨.equalityReplace f t u,rfl,rfl⟩
 simp only [UniformClosedRule12.nativeLine,h,Option.getD_some,
  GorbowProofChecker.logicalLine,GorbowLogicalAxiomCode.encode]
theorem replacementLine {arity ctx : Nat} (p : Program arity) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (f : Formula 1) (t u : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule12.lineCall tag
   (Term.numeral (n := ctx) (Encodable.encode (GorbowFormulaPrefixCode.encode f)))
   (rawNumeral t) (rawNumeral u))
   (Term.numeral (Encodable.encode (GorbowProofChecker.logicalLine (.equalityReplace f t u)))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag UniformClosedRule12.lineConstructor ht
  (Encodable.encode (GorbowFormulaPrefixCode.encode f) ::ᵥ Encodable.encode (GorbowTermPrefixCode.encode t) ::ᵥ
   Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) ctx
 rw [UniformClosedRule12.StatementChecks.exactNativeLine,nativeReplacement] at h
 simpa only [UniformClosedRule12.lineCall,rawNumeral,List.Vector.map_cons,List.Vector.map_nil] using (show Nonempty _ from ⟨h⟩)
theorem nativeReflexivity (t : Term 0) :
 TwoSol20261113.ReflexivityRecognizer.NativeProof.rawLine (GorbowTermPrefixCode.encode t) =
 GorbowProofChecker.logicalLine (.reflexive t) := by
 rfl
theorem reflexiveLine {arity ctx : Nat} (p : Program arity) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨1,RawReflexivity.lineConstructor⟩) (t : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawReflexivity.lineCall tag (rawNumeral (ctx := ctx) t))
   (Term.numeral (Encodable.encode (GorbowProofChecker.logicalLine (.reflexive t)))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag RawReflexivity.lineConstructor ht
  (Encodable.encode (GorbowTermPrefixCode.encode t) ::ᵥ nil) ctx
 rw [RawReflexivity.StatementChecks.exactNativeLine,nativeReflexivity] at h
 simpa only [RawReflexivity.lineCall,rawNumeral,List.Vector.map_cons,List.Vector.map_nil] using (show Nonempty _ from ⟨h⟩)
theorem replacement {arity ctx : Nat} (p : Program arity) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (f : Formula 1) (t u : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule12Certificate.certificate ctag tag
   (Term.numeral (n := ctx) (Encodable.encode (GorbowFormulaPrefixCode.encode f))) (rawNumeral t) (rawNumeral u))
   (Term.numeral (replacementNumber f t u)))) := by
 obtain ⟨hl⟩ := replacementLine p tag ht f t u (ctx := ctx)
 have he := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hc⟩ := PrescribedRuntimeSpecialization.PrimitiveProof.consNumeral p ctag hc
  (GorbowProofChecker.logicalLine (.equalityReplace f t u)) (ctx := ctx)
 exact ⟨Logic.trans _ _ _ he hc⟩
theorem reflexive {arity ctx : Nat} (p : Program arity) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨1,RawReflexivity.lineConstructor⟩) (t : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawCumulativeLogical.certificate ctag tag (rawNumeral (ctx := ctx) t))
   (Term.numeral (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive t)])))) := by
 obtain ⟨hl⟩ := reflexiveLine p tag ht t (ctx := ctx)
 have he := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hc⟩ := PrescribedRuntimeSpecialization.PrimitiveProof.consNumeral p ctag hc
  (GorbowProofChecker.logicalLine (.reflexive t)) (ctx := ctx)
 exact ⟨Logic.trans _ _ _ he hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.PrimitiveProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.PrimitiveProof
