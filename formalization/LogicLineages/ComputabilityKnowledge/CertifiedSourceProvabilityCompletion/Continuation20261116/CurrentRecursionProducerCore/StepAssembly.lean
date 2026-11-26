module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.UnaryCopy
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityUnderCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepAssembly
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

open CurrentImplicationCertificate
open CurrentEqualityImplication
theorem assemble {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : CurrentRecursionStepProgram.Tags)
 (H : CurrentRecursionStepProgram.Installation p base step child J)
 (P P' next next' left left' right right' output output' seed seed' congruence congruence' childCode childCode' : Term ctx)
 (hP : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal P P'))
 (hn : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal next next'))
 (hl : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal left left'))
 (hr : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal right right'))
 (ho : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal output output'))
 (hs : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal seed seed'))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal congruence congruence'))
 (hc : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal childCode childCode')) :
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal
   (CurrentRecursionStepProgram.transitivityValue J P next right output
    (CurrentRecursionStepProgram.transitivityValue J P next left right
     (CurrentRecursionStepProgram.liftValue J (equalValue J.ctag J.atag next left) P seed) congruence)
    (CurrentRecursionStepProgram.liftValue J (equalValue J.ctag J.atag right output) P childCode))
   (transitivityUnderCertificate I P' next' right' output'
    (transitivityUnderCertificate I P' next' left' right'
     (liftCertificate I (equalValue K.ctag K.atag next' left') P' seed') congruence')
    (liftCertificate I (equalValue K.ctag K.atag right' output') P' childCode')))) := by
 dsimp only
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 obtain ⟨hNL⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hn hl
 obtain ⟨hRO⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hr ho
 obtain ⟨hliftRoot⟩ := ImplicationCopy.lift p installed lhs rhs t old a x I base step child J H _ _ _ _ _ _ hNL hP hs
 obtain ⟨hfirst⟩ := TransitivityUnderCopy.certificate p installed lhs rhs t old a x I base step child J H
  _ _ _ _ _ _ _ _ _ _ _ _ hP hn hl hr hliftRoot hu
 obtain ⟨hliftChild⟩ := ImplicationCopy.lift p installed lhs rhs t old a x I base step child J H _ _ _ _ _ _ hRO hP hc
 exact TransitivityUnderCopy.certificate p installed lhs rhs t old a x I base step child J H
  _ _ _ _ _ _ _ _ _ _ _ _ hP hn hr ho hfirst hliftChild
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepAssembly
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.StepAssembly
