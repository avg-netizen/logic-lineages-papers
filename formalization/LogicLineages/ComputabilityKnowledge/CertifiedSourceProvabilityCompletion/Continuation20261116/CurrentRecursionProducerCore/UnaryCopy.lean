module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.ImplicationCopy
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.EqualityCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.UnaryCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

open CurrentImplicationCertificate
open CurrentEqualityImplication
theorem certificate {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a x)
 (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (J : CurrentRecursionStepProgram.Tags)
 (H : CurrentRecursionStepProgram.Installation p base step child J)
 {n inputs : Nat} (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (raw : List.Vector (Term ctx) inputs) (openCode left right ft fu left' right' : Term ctx)
 (hopen : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal openCode (FixedFormulaSubstitution.termValue I.previous.current.ctag I.previous.current.atag e raw f)))
 (hl : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal left left'))
 (hr : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal right right'))
 (hft : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ft (specializedValue I.previous.current.ctag I.previous.current.atag e f raw left')))
 (hfu : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal fu (specializedValue I.previous.current.ctag I.previous.current.atag e f raw right'))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionStepProgram.unaryValue J openCode left right ft fu)
   (unaryRuleCertificate I e f raw left' right'))) := by
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 obtain ⟨hP⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hl hr
 obtain ⟨hQ⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hft hft
 obtain ⟨hR⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hft hfu
 obtain ⟨hmat⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 H.hc H.ha
  I.previous.current.h_ctag I.previous.current.h_atag _ _ _ _ hft hopen
 obtain ⟨hseed⟩ := EqualityCopy.rule12 p J.ctag J.r12 K.ctag K.constructorTag H.hc H.h12
  I.previous.current.h_ctag I.previous.current.h_constructor _ _ _ _ _ _ hmat hl hr
 have hargs : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal ((ft ::ᵥ nil).get i)
   ((specializedValue K.ctag K.atag e f raw left' ::ᵥ nil).get i)) := by
  intro i
  cases i using Fin.cases with
  | zero => exact hft
  | succ i => exact Fin.elim0 i
 obtain ⟨hline⟩ := CallTransport.callCopy p RawReflexivity.lineConstructor J.reflexivityTag K.reflexivityTag
  H.hr I.previous.previous.previous.previous.previous.hreflexivity _ _ hargs
 obtain ⟨href⟩ := CallTransport.singleton p J.ctag K.rctag H.hc I.previous.previous.previous.previous.previous.hc _ _ hline
 obtain ⟨hlift⟩ := ImplicationCopy.lift p installed lhs rhs t old a x I base step child J H _ _ _ _ _ _ hQ hP href
 exact ImplicationCopy.mpUnder p installed lhs rhs t old a x I base step child J H
  _ _ _ _ _ _ _ _ _ _ hP hQ hR hseed hlift
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.UnaryCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.UnaryCopy
