module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.PropositionalCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.ImplicationCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

open CurrentImplicationCertificate
theorem lift {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : CurrentRecursionStepProgram.Tags)
 (H : CurrentRecursionStepProgram.Installation p base step child J)
 (A A' B B' code code' : Term ctx)
 (hA : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal A A'))
 (hB : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal B B'))
 (hcode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code code')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionStepProgram.liftValue J A B code) (liftCertificate I A' B' code'))) := by
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 obtain ⟨himp⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7
  H.hc H.ha I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hB hA
 obtain ⟨hprop⟩ := PropositionalCopy.certificate p false J.ctag J.ktag I.currentK.ctag I.currentK.constructorTag
  H.hc H.hk I.currentK.h_ctag I.currentK.h_constructorTag _ _ _ _ _ _ hA hB hA
 exact CallTransport.mp p J.mtag K.mtag H.hm I.previous.previous.previous.previous.previous.hmp
  _ _ _ _ _ _ himp hprop hcode

theorem mpUnder {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : CurrentRecursionStepProgram.Tags)
 (H : CurrentRecursionStepProgram.Installation p base step child J)
 (P P' Q Q' V V' hi hi' ha ha' : Term ctx)
 (hP : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal P P'))
 (hQ : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal Q Q'))
 (hV : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal V V'))
 (hhi : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal hi hi'))
 (hha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal ha ha')) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionStepProgram.mpUnderValue J P Q V hi ha) (mpUnderCertificate I P' Q' V' hi' ha'))) := by
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 obtain ⟨hPQ⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7
  H.hc H.ha I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hP hQ
 obtain ⟨hPV⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7
  H.hc H.ha I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hP hV
 obtain ⟨himp⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 7
  H.hc H.ha I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hPQ hPV
 obtain ⟨hprop⟩ := PropositionalCopy.certificate p true J.ctag J.stag I.currentS.ctag I.currentS.constructorTag
  H.hc H.hs I.currentS.h_ctag I.currentS.h_constructorTag _ _ _ _ _ _ hP hQ hV
 obtain ⟨hinner⟩ := CallTransport.mp p J.mtag K.mtag H.hm I.previous.previous.previous.previous.previous.hmp
  _ _ _ _ _ _ himp hprop hhi
 exact CallTransport.mp p J.mtag K.mtag H.hm I.previous.previous.previous.previous.previous.hmp
  _ _ _ _ _ _ hPV hinner hha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.ImplicationCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.ImplicationCopy
