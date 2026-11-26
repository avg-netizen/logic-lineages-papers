module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.QuotationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.AntecedentProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

theorem antecedent (a b : Term 1) {n ctx : Nat} (p : Program n) (ftag ctag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (LiteralSyntaxValidator.formulaCall ftag (.zero : Term ctx)
  (HistoryLookup.consCall ctag (Term.numeral 10) (Term.numeral (RawEqualityInstantiation.templateCode a b)))) (.succ .zero))) := by
 let phi : Formula 0 := .all (RawEqualityInstantiation.template a b)
 let code := Encodable.encode (GorbowFormulaPrefixCode.encode phi)
 have hv : GorbowSyntaxValidation.validFormula 0 (GorbowFormulaPrefixCode.encode phi) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 0 _).mpr
   ⟨phi,(GorbowFormulaPrefixCodeProof.decoderExact 0 _ phi).mpr rfl⟩
 have heval : evaluate LiteralSyntaxValidator.formulaValidator (0 ::ᵥ code ::ᵥ nil) = 1 := by
  rw [LiteralSyntaxValidator.NativeProof.formulaEncoded,hv]
  rfl
 obtain ⟨hval⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p ftag LiteralSyntaxValidator.formulaValidator hf (0 ::ᵥ code ::ᵥ nil) ctx
 have hvalue : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxValidator.formulaCall ftag (.zero : Term ctx) (Term.numeral code)) (.succ .zero)) := by
  simpa only [List.Vector.map_cons,List.Vector.map_nil,heval,Term.numeral,LiteralSyntaxValidator.formulaCall] using hval
 obtain ⟨hcons⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p ctag HistoryCodec.cons hc
  (10 ::ᵥ RawEqualityInstantiation.templateCode a b ::ᵥ nil) ctx
 have hcode : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.consCall ctag (Term.numeral 10 : Term ctx) (Term.numeral (RawEqualityInstantiation.templateCode a b))) (Term.numeral code)) := by
  have he : evaluate HistoryCodec.cons (10 ::ᵥ RawEqualityInstantiation.templateCode a b ::ᵥ nil) = code := by
   rw [HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
  simpa only [List.Vector.map_cons,List.Vector.map_nil,he,HistoryLookup.consCall] using hcons
 have hcall := HistoryAppend.PositiveProof.binaryCongruence ftag (.zero : Term ctx) .zero _ _
  (.logical (.reflexive .zero)) hcode
 exact ⟨Logic.trans _ _ _ hcall hvalue⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.AntecedentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.AntecedentProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.AntecedentProof.antecedent
