module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TracePrimitives
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
theorem equal {arity depth ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (a b : Term ctx) (f g : Term depth)
 (hf : Derivation T (.equal a (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode f)))))
 (hg : Derivation T (.equal b (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode g))))) :
 Nonempty (Derivation T (.equal (equalValue ctag atag a b)
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.equal f g)))))) := by
 have happ := HistoryAppend.PositiveProof.binaryCongruence atag _ _ _ _ hf hg
 have hcons := HistoryAppend.PositiveProof.binaryCongruence ctag (Term.numeral (n := ctx) 0) _ _ _
  (.logical (.reflexive _)) happ
 obtain ⟨hn⟩ := EncodingProof.equal p ctag atag hc ha _ _ f g
  (.logical (.reflexive _)) (.logical (.reflexive _)) (ctx := ctx)
 obtain ⟨hn⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hn⟩
 exact ⟨Logic.trans _ _ _ hcons hn⟩
theorem imp {arity depth ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (a b : Term ctx) (f g : Formula depth)
 (hf : Derivation T (.equal a (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (hg : Derivation T (.equal b (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode g))))) :
 Nonempty (Derivation T (.equal (impValue ctag atag a b)
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp f g)))))) := by
 have happ := HistoryAppend.PositiveProof.binaryCongruence atag _ _ _ _ hf hg
 have hcons := HistoryAppend.PositiveProof.binaryCongruence ctag (Term.numeral (n := ctx) 7) _ _ _
  (.logical (.reflexive _)) happ
 obtain ⟨hn⟩ := EncodingProof.imp p ctag atag hc ha _ _ f g
  (.logical (.reflexive _)) (.logical (.reflexive _)) (ctx := ctx)
 obtain ⟨hn⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hn⟩
 exact ⟨Logic.trans _ _ _ hcons hn⟩
theorem mp {arity ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma) (mtag : Nat)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (B implication antecedent : Term ctx) (f : Formula 0) (imp ant : Nat)
 (hb : Derivation T (.equal B
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (hi : Derivation T (.equal implication (Term.numeral imp)))
 (ha : Derivation T (.equal antecedent (Term.numeral ant))) :
 Nonempty (Derivation T
  (.equal (LiteralMPRun.certificate mtag .zero B implication antecedent)
   (Term.numeral (GorbowTheoryCertificateOperations.mpCertificate 0 (GorbowSortedSyntaxCode.formulaCode f) imp ant)))) := by
 have h := Logic.callCongruence T mtag
  ((.zero : Term ctx) ::ᵥ B ::ᵥ implication ::ᵥ antecedent ::ᵥ nil)
  ((.zero : Term ctx) ::ᵥ Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)) ::ᵥ Term.numeral imp ::ᵥ Term.numeral ant ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive (.zero : Term ctx))
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => cases i using Fin.cases with
       | zero => exact hi
       | succ i => cases i using Fin.cases with
         | zero => exact ha
         | succ i => exact Fin.elim0 i)
 obtain ⟨hn⟩ := PrescribedRuntimeSpecialization.PrimitiveProof.mpNumeral (ctx := ctx) p mtag hm f imp ant
 obtain ⟨hn⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hn⟩
 exact ⟨Logic.trans _ _ _ h hn⟩
theorem replacement {arity ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma)
 (ctag tag : Nat) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hq : (nodes p)[tag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (A a b : Term ctx) (f : Formula 1) (t u : Term 0)
 (hA : Derivation T (.equal A (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (ha : Derivation T (.equal a (rawNumeral t))) (hb : Derivation T (.equal b (rawNumeral u))) :
 Nonempty (Derivation T (.equal (UniformClosedRule12Certificate.certificate ctag tag A a b)
  (Term.numeral (replacementNumber f t u)))) := by
 have hl := Logic.callCongruence T tag (A ::ᵥ a ::ᵥ b ::ᵥ nil)
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)) ::ᵥ rawNumeral t ::ᵥ rawNumeral u ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hA
   | succ i => cases i using Fin.cases with
     | zero => exact ha
     | succ i => cases i using Fin.cases with
       | zero => exact hb
       | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := PrescribedRuntimeEquality.PrimitiveProof.replacement p ctag tag hc hq f t u (ctx := ctx)
 obtain ⟨hn⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hn⟩
 exact ⟨Logic.trans _ _ _ hs hn⟩
theorem reflexive {arity ctx : Nat} (p : Program arity)
 (T : Sentence → Prop) (hT : ∀ sigma, GorbowPRNumeralCalculation.Theory p sigma → T sigma) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (raw : Term ctx) (t : Term 0)
 (hr : Derivation T (.equal raw (rawNumeral t))) :
 Nonempty (Derivation T
  (.equal (RawCumulativeLogical.certificate ctag tag raw)
   (Term.numeral (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive t)])))) := by
 have hl := Logic.callCongruence T tag
  (raw ::ᵥ nil) (rawNumeral t ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hr
   | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := PrescribedRuntimeEquality.PrimitiveProof.reflexive p ctag tag hc ht t (ctx := ctx)
 obtain ⟨hn⟩ := GorbowTheoryProofProof.monotonicity _ T hT ctx _ ⟨hn⟩
 exact ⟨Logic.trans _ _ _ hs hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TracePrimitives
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TracePrimitives
