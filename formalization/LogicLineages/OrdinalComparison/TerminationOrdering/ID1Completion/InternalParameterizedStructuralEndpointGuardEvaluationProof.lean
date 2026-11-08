module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardEvaluationProof
open Source NumberedRewriteReduction NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative
open InternalParameterizedStructuralEndpointGuard
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open InternalStructuralEndpointGuardEvaluationProof (packedTag)
open InternalOriginalUniformDescentSelectionEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem atEvaluation (P : Program 2) (i : Fin 6) (v : List.Vector Nat 6) :
    evaluate (atParameter P i) v = evaluate P (List.Vector.ofFn ![v.get i,v.get 5]) := rfl

theorem typeGuardEvaluation (v : List.Vector Nat 6) :
    evaluate typeGuard v =
      if (Nat.unpair (v.get 2)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
        (Nat.unpair (v.get 3)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
        (Nat.unpair (v.get 4)).1 = v.get 0 then 1 else 0 := by
  change evaluate InternalApplicationStepPeel.endpointTypeGuard
    (List.Vector.ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4]) = _
  rw [InternalStructuralEndpointGuardEvaluationProof.typeGuardEvaluation]
  rfl

/-- The old decoder analysis is unchanged. Only the actual binary selected
leaf evaluations at the common encoded parameter replace the unary leaves. -/
theorem actualOriginalParameterizedStructuralEndpointCalibration :
    InternalParameterizedStructuralEndpointGuardTargets.ActualOriginalParameterizedStructuralEndpointCalibration := by
  intro n arity data hc symbols S Gamma table v
  obtain ⟨sigma,hd,hdn⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 0)
  obtain ⟨tau,he,hen⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 1)
  have hs := (actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table (v.get 2)).2
  have ht := (actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table (v.get 3)).1
  have ha := (actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table (v.get 4)).2
  have hm := (leafSlice n arity data hc symbols S Gamma table (v.get 1)).2.2.2
  simp only [selectedEndpoint,endpoint,conjunctionEvaluation,atEvaluation,typeGuardEvaluation]
  change (if evaluate (validity data)
      (List.Vector.ofFn ![v.get 2,parameterCode symbols S Gamma table]) = 1 ∧
      (if evaluate (targetValidity data)
        (List.Vector.ofFn ![v.get 3,parameterCode symbols S Gamma table]) = 1 ∧
        (if evaluate (validity data)
          (List.Vector.ofFn ![v.get 4,parameterCode symbols S Gamma table]) = 1 ∧
          (if (if (Nat.unpair (v.get 2)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
              (Nat.unpair (v.get 3)).1 = 1 + Nat.pair (v.get 0) (v.get 1) ∧
              (Nat.unpair (v.get 4)).1 = v.get 0 then 1 else 0) = 1 ∧
            evaluate data.member
              (List.Vector.ofFn ![v.get 1,parameterCode symbols S Gamma table]) = 1
            then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0) = 1
      then 1 else 0) = _
  simp only [hs,ht,ha,hm]
  simp only [InternalOriginalStepGuard.sourceValidityValue,
    InternalOriginalStepGuard.targetValidityValue,rawCarrierTest,
    InternalStructuralEndpointGuard.membershipValue,he]
  cases hq : decodeUniverse n arity symbols S Gamma (v.get 2) with
  | none => simp [InternalApplicationStepPeel.endpointValue,hd,he,hq]
  | some q =>
    cases hr : decodePackedNumber n arity Gamma (v.get 3) with
    | none => simp [InternalApplicationStepPeel.endpointValue,hd,he,hq,hr]
    | some r =>
      cases hb : decodeUniverse n arity symbols S Gamma (v.get 4) with
      | none => simp [InternalApplicationStepPeel.endpointValue,hd,he,hq,hr,hb]
      | some a =>
        have hqt := packedTag n arity Gamma (v.get 2) q (Option.filter_eq_some_iff.mp hq).1
        have hrt := packedTag n arity Gamma (v.get 3) r hr
        have hat := packedTag n arity Gamma (v.get 4) a (Option.filter_eq_some_iff.mp hb).1
        have harrow : 1 + Nat.pair (v.get 0) (v.get 1) = typeNumber (.arrow sigma tau) := by
          simp only [typeNumber,hdn,hen]
        rw [hqt,hrt,hat,harrow,← hdn]
        have hi := NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective
        simp only [InternalApplicationStepPeel.endpointValue,hd,he,hq,hr,hb,
          Option.isSome_some,Bool.toNat_true,hi.eq_iff]
        by_cases hqs : q.1 = .arrow sigma tau <;>
          by_cases hrs : r.1 = .arrow sigma tau <;>
          by_cases has : a.1 = sigma <;> by_cases hmem : tau ∈ S <;>
          simp [hqs,hrs,has,hmem]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardEvaluationProof
