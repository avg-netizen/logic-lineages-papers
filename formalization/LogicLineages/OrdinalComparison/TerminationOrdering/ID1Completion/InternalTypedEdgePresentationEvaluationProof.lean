module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationEvaluationProof
open Source NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative NumberedTypedCarrier
open InternalTypedEdgePresentation InternalApplicationCertificateConstructors
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original typed acceptance already puts the requested root type in S,
without subtype closure. This is used only for external calibration. -/
theorem originalAcceptanceMembership (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (v : List.Vector Nat 2)
    (h : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 1) :
    InternalStructuralEndpointGuard.membershipValue S (v.get 1) = 1 := by
  obtain ⟨tau,ht,htn⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 1)
  cases hq : decodeUniverse n arity symbols S Gamma (v.get 0) with
  | none =>
    simp only [InternalOriginalTypedCarrier.typedValue,ht,Option.any_some,
      typedCanonicalCarrierTest,hq,Option.any_none,Bool.toNat_false,Nat.zero_ne_one] at h
  | some q =>
    have hb : q.1 = tau ∧ representativeCode symbols S q = v.get 0 := by
      simpa only [InternalOriginalTypedCarrier.typedValue,ht,Option.any_some,
        typedCanonicalCarrierTest,hq,OrdinaryArithmeticQuotientProof.boolNatOne,
        decide_eq_true_eq] using h
    have hu := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
      (v.get 0) q).mp hq
    have hr := NumberedUniverseOperationsProof.rootType (fun t => t ∈ S)
      (NumberedFiniteUniverse.HeadInWindow arity symbols S) q.2 hu.2
    have hm : tau ∈ S := hb.1 ▸ hr
    simp only [InternalStructuralEndpointGuard.membershipValue,ht,hm,decide_true,Bool.toNat_true]

theorem membershipAtEvaluation (member : Program 1) (v : List.Vector Nat 2) :
    evaluate (membershipAt member) v =
      evaluate member (List.Vector.ofFn ![v.get 1]) := rfl

theorem actualOriginalMembershipTypedCalibration :
    InternalTypedEdgePresentationTargets.ActualOriginalMembershipTypedCalibration := by
  intro n arity symbols S Gamma validity member oldTyped hv hm ho v
  have ht := InternalOriginalTypedCarrierProof.actualOriginalTypedWrapperCalibration
    n arity symbols S Gamma validity oldTyped hv ho
  have hbool : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 0 ∨
      InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 1 := by
    unfold InternalOriginalTypedCarrier.typedValue
    cases (decodeType (v.get 1)).any (fun tau =>
      typedCanonicalCarrierTest n arity symbols S Gamma tau (v.get 0)) <;> simp
  rcases hbool with hz | hone
  · rw [typedChecker,conjunctionEvaluation,ht,hz]
    simp
  · have hm' := hm (List.Vector.ofFn ![v.get 1])
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero] at hm'
    rw [typedChecker,conjunctionEvaluation,ht,membershipAtEvaluation,hm',
      originalAcceptanceMembership n arity symbols S Gamma v hone,hone]
    simp

/-- The chosen ASTs share the same leaves. Calibration never identifies
internal graph predicates of distinct Programs. -/
theorem presentationCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : Data) (hc : Calibrated n arity symbols S Gamma table data) :
    PresentationCalibrated n arity symbols S Gamma table data := by
  have he := InternalStructuralEndpointGuardProof.actualOriginalStructuralEndpointCalibration
    n arity symbols S Gamma data.validity data.member hc.1 hc.2.1
  have hn := InternalApplicationStepCheckerProof.actualOriginalCheckerCalibration
    n arity symbols S Gamma table (endpoint data) data.oldEdge.stepProgram he hc.2.2.1.1
  have hs := InternalOriginalStepGuardProof.actualOriginalGuardedStepCalibration
    n arity symbols S Gamma table data.validity
    (InternalApplicationStepPeel.checker (endpoint data) data.oldEdge.stepProgram) hc.1 hn
  let raw : InternalQuotientEdgeChecker.Data :=
    { stepProgram := stepChecker data,
      sourceRepresentative := data.oldEdge.sourceRepresentative,
      targetRepresentative := data.oldEdge.targetRepresentative }
  have hr : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table raw :=
    ⟨hs,hc.2.2.1.2⟩
  have hedge : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table (edgeData data) :=
    InternalRepresentativeTagProof.actualOriginalRepresentativeWrapperCalibration
      n arity symbols S Gamma table data.validity raw hc.1 hr
  exact ⟨he,hedge,actualOriginalMembershipTypedCalibration n arity symbols S Gamma
    data.validity data.member data.oldTyped hc.1 hc.2.1 hc.2.2.2,
    InternalQuotientEdgeCheckerEvaluationProof.actualOriginalCheckerCalibration
      n arity symbols S Gamma table (edgeData data) hedge⟩

theorem calibratedDataExists (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    ∃ data : Data, Calibrated n arity symbols S Gamma table data := by
  obtain ⟨validity,hv⟩ := InternalOriginalStepGuardProof.actualOriginalValidityProgramsExist
    n arity symbols S Gamma
  obtain ⟨member,hm⟩ := InternalStructuralEndpointGuardProof.actualOriginalMembershipProgramExists S
  obtain ⟨oldEdge,he⟩ := InternalQuotientEdgeCheckerEvaluationProof.actualOriginalProgramsExist
    n arity symbols S Gamma table
  obtain ⟨oldTyped,ht⟩ := InternalOriginalTypedCarrierProof.actualOriginalTypedProgramExists
    n arity symbols S Gamma
  exact ⟨⟨validity,member,oldEdge,oldTyped⟩,hv,hm,he,ht⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationEvaluationProof
