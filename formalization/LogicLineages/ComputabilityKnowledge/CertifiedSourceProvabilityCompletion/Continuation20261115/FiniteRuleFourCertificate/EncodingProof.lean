module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
/-- Exact closed syntax, not a quotation convention change. -/
theorem closedIdentity (sigma : Sentence) : weakenClosed 0 sigma = sigma :=
 GorbowClosedDeductionProof.closedSyntax.1 sigma
theorem sortedCode (sigma : Sentence) :
 GorbowSortedSyntaxCode.formulaCode sigma = rawCode sigma + rawCode sigma := by
 simp only [GorbowSortedSyntaxCode.formulaCode,GorbowSortedSyntaxCode.tagFormula,
  GorbowCodeConstructors.formulaNumber,GorbowCodeConstructors.number,rawCode,two_mul]
def tailCode (sigma : Sentence) : Nat :=
 Encodable.encode ((4,0,[GorbowFormulaPrefixCode.encode sigma],0,0) : Nat × GorbowProofChecker.Payload)

theorem lineNumber (sigma : Sentence) :
 FiniteRuleFourLeaf.lineCode sigma = Nat.pair 0 (Nat.pair (rawCode sigma) (tailCode sigma)) := by
 simp only [FiniteRuleFourLeaf.lineCode,GorbowTheoryChecker.axiomLine,closedIdentity,
  tailCode,rawCode,HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat]
/-- Original cons encoding computes the literal singleton certificate. -/
theorem certificate {n ctx : Nat} (p : Program n) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (sigma : Sentence) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.consCall ctag (Term.numeral (n := ctx) (FiniteRuleFourLeaf.lineCode sigma)) .zero)
   (Term.numeral (certificateCode sigma)))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p ctag HistoryCodec.cons hc
  (FiniteRuleFourLeaf.lineCode sigma ::ᵥ 0 ::ᵥ nil) ctx
 rw [HistoryCodec.NativeProof.nativeConsAllVectors] at h
 simpa only [HistoryLookup.consCall,certificateCode,FiniteRuleFourLeaf.lineCode,
  HistoryLookup.NativeProof.encodeCons,List.Vector.map_cons,List.Vector.map_nil,
  List.Vector.head_cons,List.Vector.tail_cons,Term.numeral] using (show Nonempty _ from ⟨h⟩)
theorem pair {n ctx : Nat} (p : Program n) (ptag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryKernel.pairCall ptag (Term.numeral (n := ctx) a) (Term.numeral b))
   (Term.numeral (Nat.pair a b)))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p ptag HistoryCodec.pair hp (a ::ᵥ b ::ᵥ nil) ctx
 rw [HistoryCodec.NativeProof.nativePair] at h
 simpa only [HistoryKernel.pairCall,List.Vector.map_cons,List.Vector.map_nil,
  List.Vector.head_cons,List.Vector.tail_cons] using (show Nonempty _ from ⟨h⟩)
/-- Internal source arithmetic for the exact sorted formula code. -/
theorem formula {ctx : Nat} (T : Sentence → Prop) (sigma : Sentence) :
 Nonempty (Derivation T (.equal (Term.numeral (n := ctx) (GorbowSortedSyntaxCode.formulaCode sigma))
  (.add (Term.numeral (rawCode sigma)) (Term.numeral (rawCode sigma))))) := by
 obtain ⟨h⟩ := QuotedVerifierMP.QuotationProof.numeralAdd T ctx (rawCode sigma) (rawCode sigma)
 rw [sortedCode]
 exact ⟨Support.equalitySymmetry _ _ h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourCertificate.EncodingProof
