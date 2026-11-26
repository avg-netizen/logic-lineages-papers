module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.ImplicationCopy
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.EqualityCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityUnderCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

open CurrentImplicationCertificate
open CurrentEqualityImplication
theorem certificate {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : CurrentRecursionStepProgram.Tags)
 (H : CurrentRecursionStepProgram.Installation p base step child J)
 (P P' left left' middle middle' right right' first first' second second' : Term ctx)
 (hP : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal P P'))
 (hl : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal left left'))
 (hm : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal middle middle'))
 (hr : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal right right'))
 (hf : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal first first'))
 (hs : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal second second')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionStepProgram.transitivityValue J P left middle right first second)
   (transitivityUnderCertificate I P' left' middle' right' first' second'))) := by
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 obtain ⟨hTU⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hl hm
 obtain ⟨hUV⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hm hr
 obtain ⟨hTV⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hl hr
 obtain ⟨hmat⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1))))) hl (.logical (.reflexive _))
 obtain ⟨hseed⟩ := EqualityCopy.rule12 p J.ctag J.r12 K.ctag K.constructorTag H.hc H.h12
  I.previous.current.h_ctag I.previous.current.h_constructor _ _ _ _ _ _ hmat hm hr
 obtain ⟨himp⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hTU hTV
 obtain ⟨hfull⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hUV himp
 obtain ⟨hlift⟩ := ImplicationCopy.lift p installed lhs rhs t old a x I base step child J H _ _ _ _ _ _ hfull hP hseed
 obtain ⟨hfirst⟩ := ImplicationCopy.mpUnder p installed lhs rhs t old a x I base step child J H
  _ _ _ _ _ _ _ _ _ _ hP hUV himp hlift hs
 exact ImplicationCopy.mpUnder p installed lhs rhs t old a x I base step child J H
  _ _ _ _ _ _ _ _ _ _ hP hTU hTV hfirst hf
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityUnderCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityUnderCopy
