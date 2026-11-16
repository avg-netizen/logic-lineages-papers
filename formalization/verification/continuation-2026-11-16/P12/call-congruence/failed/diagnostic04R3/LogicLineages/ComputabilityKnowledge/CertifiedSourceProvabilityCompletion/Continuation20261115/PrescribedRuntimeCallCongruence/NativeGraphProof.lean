module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
theorem replacement {arity ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hq : (nodes p)[J.constructorTag]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (A left right : Term ctx) (f : Formula 1) (t u : Term 0)
 (hA : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal A (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal left (rawNumeral t)))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal right (rawNumeral u))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule12Certificate.certificate J.ctag J.constructorTag A left right)
   (Term.numeral (replacementNumber f t u)))) := by
 have hl := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) J.constructorTag
  (A ::ᵥ left ::ᵥ right ::ᵥ nil)
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)) ::ᵥ rawNumeral t ::ᵥ rawNumeral u ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact hA
   | succ i => cases i using Fin.cases with
     | zero => exact ht
     | succ i => cases i using Fin.cases with
       | zero => exact hu
       | succ i => exact Fin.elim0 i)
 have hs := HistoryAppend.PositiveProof.binaryCongruence J.ctag _ _ (.zero : Term ctx) .zero hl (.logical (.reflexive .zero))
 obtain ⟨hn⟩ := PrescribedRuntimeEquality.PrimitiveProof.replacement p J.ctag J.constructorTag hc hq f t u (ctx := ctx)
 exact ⟨Logic.trans _ _ _ hs hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeGraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.NativeGraphProof
