module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.EqualityCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

theorem certificate {arity ctx : Nat} (p : Program arity) (m c a r m' c' a' r' : Nat)
 (hm : (nodes p)[m]? = some ⟨4,LiteralRawMP.constructor⟩)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (hr : (nodes p)[r]? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (hm' : (nodes p)[m']? = some ⟨4,LiteralRawMP.constructor⟩)
 (hc' : (nodes p)[c']? = some ⟨2,HistoryCodec.cons⟩)
 (ha' : (nodes p)[a']? = some ⟨2,HistoryAppend.append⟩)
 (hr' : (nodes p)[r']? = some ⟨3,UniformClosedRule12.lineConstructor⟩)
 (t t' u u' v v' first first' second second' : Term ctx)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal t t'))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal u u'))
 (hv : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal v v'))
 (hfirst : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal first first'))
 (hsecond : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal second second')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (transitivityCertificate m c a r t u v first second)
   (transitivityCertificate m' c' a' r' t' u' v' first' second'))) := by
 obtain ⟨htv⟩ := CurrentCompositionCertificate.CodecProof.binary p c a c' a' 0 hc ha hc' ha' _ _ _ _ ht hv
 obtain ⟨htu⟩ := CurrentCompositionCertificate.CodecProof.binary p c a c' a' 0 hc ha hc' ha' _ _ _ _ ht hu
 obtain ⟨himp⟩ := CurrentCompositionCertificate.CodecProof.binary p c a c' a' 7 hc ha hc' ha' _ _ _ _ htu htv
 obtain ⟨hmat⟩ := CurrentCompositionCertificate.CodecProof.binary p c a c' a' 0 hc ha hc' ha' _ _
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1))))) ht (.logical (.reflexive _))
 obtain ⟨hrule⟩ := EqualityCopy.rule12 p c r c' r' hc hr hc' hr' _ _ _ _ _ _ hmat hu hv
 obtain ⟨hinner⟩ := CallTransport.mp p m m' hm hm' _ _ _ _ _ _ himp hrule hsecond
 exact CallTransport.mp p m m' hm hm' _ _ _ _ _ _ htv hinner hfirst
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityCopy
