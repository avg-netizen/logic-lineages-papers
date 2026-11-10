module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedApplicationFactorizationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNativeFoldProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedNumericDecoding NumberedNumericCarrier NumberedQuotientApplication NumberedAuxiliaryCoding
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalResultFold (rootGuard leaf rawApplicationAt)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationValidityStack InternalApplicationValidityStackStateProof
open InternalParameterizedApplicationResultFoldCalibration
open InternalParameterizedApplicationResultFoldCalibrationProof
open InternalOriginalUniformCanonicalResultFoldSupportProof (rootGuardSource)
open InternalRepresentativeFoldCalibrationSupportProof (targetOnPacked applicationSelectors)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open InternalOriginalStepGuard (sourceValidityValue)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- The paid exact numeric factorization, not a second selected-leaf
application, calibrates the literal raw combiner on original typed children. -/
theorem rawTypedApplication (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse symbols S f) (ha : InUniverse symbols S a) (parameter : Nat) :
    evaluate rawApplicationAt (ofFn ![typeNumber sigma,typeNumber tau,
      representativeCode symbols S ⟨.arrow sigma tau,f⟩,
      representativeCode symbols S ⟨sigma,a⟩,parameter]) =
      representativeCode symbols S (applicationPacked f a) := by
  change evaluate application (ofFn ![typeNumber sigma,typeNumber tau,
    representativeCode symbols S ⟨.arrow sigma tau,f⟩,
    representativeCode symbols S ⟨sigma,a⟩]) = _
  rw [applicationEvaluation]
  exact (NumberedApplicationFactorizationProof.actualRepresentativeApplicationFactorization
    n arity symbols S hS Gamma sigma tau f a hf ha).symm

/-- Source decoding recovers actual typed universe children. The caller's
arbitrary raw parameter remains the fifth combiner argument throughout. -/
theorem rawOpenedRoot (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S)) (Gamma : List Ty)
    (value parameter : Nat) (ht : tagValue value = 2)
    (hs : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate rawApplicationAt (ofFn ![domainValue value,resultTypeValue value,
      targetRepresentativeValue n arity symbols S Gamma (functionChildValue value),
      targetRepresentativeValue n arity symbols S Gamma (argumentChildValue value),parameter]) =
      targetRepresentativeValue n arity symbols S Gamma value := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hs
  | some q =>
    obtain ⟨hnum,hq⟩ :=
      (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd
    rcases q with ⟨tau,q⟩
    rw [← hnum] at ht ⊢
    cases q with
    | app f a =>
      have hf : InUniverse symbols S f := ⟨hq.1.2.1,hq.2.1⟩
      have ha : InUniverse symbols S a := ⟨hq.1.2.2,hq.2.2⟩
      have hsel := applicationSelectors f a
      simp only [applicationPacked] at hsel
      rw [hsel.1,hsel.2.1,hsel.2.2.1,hsel.2.2.2,
        targetOnPacked,targetOnPacked,targetOnPacked]
      exact rawTypedApplication n arity symbols S hS Gamma _ _ f a hf ha parameter
    | _ => simp [tagValue,payloadValue,packedNumber,termCode,codeNumber] at ht

/-- Native strong induction uses original INPUT payloads. One decoded
Gamma/object slice works for every recursive input; unopened roots retain
the calibrated whole selected leaf, including malformed source values. -/
theorem semanticAtDecoded (n : Nat) (arity : Fin n → Nat) (data : Data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hS : SubtypeClosed (fun tau => tau ∈ ctx.1.2))
    (decoded : DecodedSourceCalibration.DecodedCalibration n arity data parameter ctx Gamma)
    (value : Nat) :
    semanticFoldP (rootGuard data) (leaf data) rawApplicationAt value parameter =
      targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value := by
  have hsource (x : Nat)
      (hop : tagValue x = 2 ∧ evaluate (rootGuard data) (ofFn ![x,parameter]) = 1) :
      sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma x = 1 := by
    have hs := rootGuardSource data x parameter hop.2
    rw [decoded.sourceValidity x] at hs
    exact hs
  suffices allPayloads : ∀ bound x : Nat, payloadValue x = bound →
      semanticFoldP (rootGuard data) (leaf data) rawApplicationAt x parameter =
        targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma x by
    exact allPayloads (payloadValue value) value rfl
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
    intro x hbound
    rw [actualOriginalParameterizedSemanticResultFoldEquation]
    by_cases hop : tagValue x = 2 ∧ evaluate (rootGuard data) (ofFn ![x,parameter]) = 1
    · rw [if_pos hop]
      have hb := applicationPayloadBound x hop.1
      have hf : payloadValue (functionChildValue x) < bound := by
        rw [functionChildPayload]
        omega
      have ha : payloadValue (argumentChildValue x) < bound := by
        rw [argumentChildPayload]
        omega
      rw [ih (payloadValue (functionChildValue x)) hf (functionChildValue x) rfl,
        ih (payloadValue (argumentChildValue x)) ha (argumentChildValue x) rfl]
      exact rawOpenedRoot n arity ctx.1.1 ctx.1.2 hS Gamma x parameter hop.1 (hsource x hop)
    · rw [if_neg hop]
      exact decoded.representative x

/-- The existing all-input bounded-stack calibration relates the concrete
unchanged stack to the native semantic fold. No internal judgment is inferred. -/
theorem foldAtDecoded (n : Nat) (arity : Fin n → Nat) (data : Data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hS : SubtypeClosed (fun tau => tau ∈ ctx.1.2))
    (decoded : DecodedSourceCalibration.DecodedCalibration n arity data parameter ctx Gamma)
    (value : Nat) :
    evaluate (InternalParameterizedApplicationResultStack.foldP
      (rootGuard data) (leaf data) rawApplicationAt) (ofFn ![value,parameter]) =
      targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value := by
  exact (actualOriginalParameterizedBoundedResultFoldCalibration
    (rootGuard data) (leaf data) rawApplicationAt value parameter).2.trans
    (semanticAtDecoded n arity data parameter ctx Gamma hS decoded value)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNativeFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNativeFoldProof
