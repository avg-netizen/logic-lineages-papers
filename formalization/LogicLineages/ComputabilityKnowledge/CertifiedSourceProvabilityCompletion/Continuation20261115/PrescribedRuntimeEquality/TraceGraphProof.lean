module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.PrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem replacement {arity ctx : Nat} (p : Program arity) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (A : Term ctx) (f : Formula 1) (t u : Term 0)
 (hA : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal A (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule12Certificate.certificate ctag tag A (rawNumeral t) (rawNumeral u))
   (Term.numeral (replacementNumber f t u)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 have hl := Logic.callCongruence T tag
  (A ::ᵥ rawNumeral t ::ᵥ rawNumeral u ::ᵥ nil)
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)) ::ᵥ rawNumeral t ::ᵥ rawNumeral u ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact hA
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive (rawNumeral t))
     | succ i => cases i using Fin.cases with
       | zero => exact .logical (.reflexive (rawNumeral u))
       | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := PrimitiveProof.replacement p ctag tag hc ht f t u (ctx := ctx)
 exact ⟨Logic.trans _ _ _ hs hn⟩
theorem reflexive {arity ctx : Nat} (p : Program arity) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨1,RawReflexivity.lineConstructor⟩)
 (raw : Term ctx) (t : Term 0)
 (hr : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal raw (rawNumeral t))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (RawCumulativeLogical.certificate ctag tag raw)
   (Term.numeral (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive t)])))) := by
 have hl := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) tag
  (raw ::ᵥ nil) (rawNumeral t ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hr
   | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := PrimitiveProof.reflexive p ctag tag hc ht t (ctx := ctx)
 exact ⟨Logic.trans _ _ _ hs hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceGraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.TraceGraphProof
