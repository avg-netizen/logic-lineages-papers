module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AxiomTrace
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph

theorem binaryNumber {arity ctx : Nat} (p : Program arity) (q : Program 2) (tag : Nat)
 (hq : (nodes p)[tag]? = some ⟨2,q⟩) (a b : Term ctx) (x y : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (Term.numeral x)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (Term.numeral y))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (a ::ᵥ b ::ᵥ nil)) (Term.numeral (evaluate q (x ::ᵥ y ::ᵥ nil))))) := by
 have he := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) tag
  (a ::ᵥ b ::ᵥ nil) (Term.numeral x ::ᵥ Term.numeral y ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact ha
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => exact Fin.elim0 i)
 obtain ⟨hn⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p tag q hq (x ::ᵥ y ::ᵥ nil) ctx
 exact ⟨Logic.trans _ _ _ he hn⟩

theorem pair {arity ctx : Nat} (p : Program arity) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) (x y : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (Term.numeral x)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (Term.numeral y))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryKernel.pairCall tag a b) (Term.numeral (Nat.pair x y)))) := by
 have h := binaryNumber p HistoryCodec.pair tag hp a b x y ha hb
 rw [LiteralRawMP.NativeProof.pairEval] at h
 exact h

theorem cons {arity ctx : Nat} (p : Program arity) (tag : Nat)
 (hp : (nodes p)[tag]? = some ⟨2,HistoryCodec.cons⟩) (a b : Term ctx) (x y : Nat)
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (Term.numeral x)))
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (Term.numeral y))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (HistoryLookup.consCall tag a b) (Term.numeral (Nat.pair x y).succ))) := by
 have h := binaryNumber p HistoryCodec.cons tag hp a b x y ha hb
 rw [CurrentRecursionBaseProgram.NativePrimitives.consEval] at h
 exact h

theorem axiomCode {arity ctx : Nat} (p : Program arity) (J : CurrentRecursionBaseProgram.Tags)
 (hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (raw : Term ctx) (f : Formula 0)
 (hf : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal raw (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionBaseProgram.axiomValue J raw) (Term.numeral (FiniteRuleFourCertificate.certificateCode f)))) := by
 have hz : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (.zero : Term ctx) (Term.numeral 0)) := .logical (.reflexive _)
 have hfour : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (Term.numeral (n := ctx) 4) (Term.numeral 4)) := .logical (.reflexive _)
 obtain ⟨hargs⟩ := cons p J.ctag hc raw .zero _ 0 hf hz
 obtain ⟨h0⟩ := pair p J.ptag hp .zero .zero 0 0 hz hz
 obtain ⟨h1⟩ := pair p J.ptag hp _ _ _ _ hargs h0
 obtain ⟨h2⟩ := pair p J.ptag hp .zero _ 0 _ hz h1
 obtain ⟨h3⟩ := pair p J.ptag hp (Term.numeral 4) _ 4 _ hfour h2
 obtain ⟨h4⟩ := pair p J.ptag hp raw _ _ _ hf h3
 obtain ⟨h5⟩ := pair p J.ptag hp .zero _ 0 _ hz h4
 obtain ⟨hcert⟩ := cons p J.ctag hc _ .zero _ 0 h5 hz
 have hnilNat : Encodable.encode ([] : List Nat) = 0 := rfl
 have hnilArgs : Encodable.encode ([] : List (List Nat)) = 0 := rfl
 have hnilLine : Encodable.encode ([] : List GorbowProofChecker.Line) = 0 := rfl
 simpa only [CurrentRecursionBaseProgram.axiomValue,FiniteRuleFourCertificate.certificateCode,
  GorbowTheoryChecker.axiomLine,FiniteRuleFourCertificate.EncodingProof.closedIdentity,
  HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,HistoryLookup.NativeProof.encodeCons,hnilNat,hnilArgs,hnilLine]
  using (show Nonempty _ from ⟨hcert⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AxiomTrace
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AxiomTrace
