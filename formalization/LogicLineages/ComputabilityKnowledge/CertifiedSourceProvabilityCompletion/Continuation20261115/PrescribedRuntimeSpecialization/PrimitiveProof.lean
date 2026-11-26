module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.PrimitiveProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Literal original line equality, obtained from original case13 compilation. -/
theorem nativeLine (f : Formula 1) (t : Term 0) :
 UniformClosedRule13.nativeLine (GorbowFormulaPrefixCode.encode f) (GorbowTermPrefixCode.encode t) =
 GorbowProofChecker.logicalLine (.allInstantiate f t) := by
 have h : GorbowLogicalAxiomCode.case13 0 [GorbowFormulaPrefixCode.encode f,GorbowTermPrefixCode.encode t] =
  some (GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (.allInstantiate f t))) :=
  (GorbowLogicalAxiomCodeProof.exactCompilation 0 _ _).mpr ⟨.allInstantiate f t,rfl,rfl⟩
 simp only [UniformClosedRule13.nativeLine,h,Option.getD_some,
  GorbowProofChecker.logicalLine,GorbowLogicalAxiomCode.encode]
theorem lineNumeral {arity ctx : Nat} (p : Program arity) (tag : Nat)
 (ht : (nodes p)[tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (f : Formula 1) (t : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule13.lineCall tag
   (Term.numeral (n := ctx) (Encodable.encode (GorbowFormulaPrefixCode.encode f)))
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t))))
   (Term.numeral (Encodable.encode (GorbowProofChecker.logicalLine (.allInstantiate f t)))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag UniformClosedRule13.lineConstructor ht
  (Encodable.encode (GorbowFormulaPrefixCode.encode f) ::ᵥ Encodable.encode (GorbowTermPrefixCode.encode t) ::ᵥ nil) ctx
 rw [UniformClosedRule13.StatementChecks.exactNativeLine,nativeLine] at h
 simpa only [UniformClosedRule13.lineCall,List.Vector.map_cons,List.Vector.map_nil] using (show Nonempty _ from ⟨h⟩)
theorem consNumeral {arity ctx : Nat} (p : Program arity) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (line : GorbowProofChecker.Line) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.consCall ctag (Term.numeral (n := ctx) (Encodable.encode line)) .zero)
   (Term.numeral (GorbowNumericCertificate.certificateNumber [line])))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p ctag HistoryCodec.cons hc
  (Encodable.encode line ::ᵥ 0 ::ᵥ nil) ctx
 rw [HistoryCodec.NativeProof.nativeConsAllVectors] at h
 have hnil : Encodable.encode ([] : List GorbowProofChecker.Line) = 0 := rfl
 simpa only [hnil,HistoryLookup.consCall,GorbowNumericCertificate.certificateNumber,
  HistoryLookup.NativeProof.encodeCons,List.Vector.map_cons,List.Vector.map_nil,
  List.Vector.head_cons,List.Vector.tail_cons,Term.numeral] using (show Nonempty _ from ⟨h⟩)
theorem mpNumeral {arity ctx : Nat} (p : Program arity) (mtag : Nat)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (f : Formula 0) (imp ant : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralMPRun.certificate mtag (.zero : Term ctx)
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))) (Term.numeral imp) (Term.numeral ant))
   (Term.numeral (GorbowTheoryCertificateOperations.mpCertificate 0 (GorbowSortedSyntaxCode.formulaCode f) imp ant)))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p mtag LiteralRawMP.constructor hm
  (0 ::ᵥ Encodable.encode (GorbowFormulaPrefixCode.encode f) ::ᵥ imp ::ᵥ ant ::ᵥ nil) ctx
 rw [LiteralRawMP.StatementChecks.exactNativeEven] at h
 simpa only [LiteralMPRun.certificate,List.Vector.map_cons,List.Vector.map_nil,Term.numeral,
  GorbowSortedSyntaxCode.formulaRawNumber,GorbowSortedSyntaxCode.formulaCode,GorbowCodeConstructors.formulaNumber] using (show Nonempty _ from ⟨h⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.PrimitiveProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.PrimitiveProof
