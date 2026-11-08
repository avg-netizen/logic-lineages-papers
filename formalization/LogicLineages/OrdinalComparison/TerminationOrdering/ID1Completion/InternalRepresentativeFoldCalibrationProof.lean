module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationProof
open Source InternalRepresentativeFoldCalibration InternalOriginalStepGuard InternalQuotientEdgeChecker
open InternalRepresentativeFoldCalibrationSupportProof InternalRepresentativeFoldCalibrationSemanticProof
open InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (exactOneEvaluation zeroEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem unaryVector (v : List.Vector Nat 1) : v = List.Vector.ofFn ![v.get 0] := by
  apply List.Vector.ext
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  simp

/-- The generic bounded fold calibration is consumed here as its checked
supplier theorem. No corresponding premise is added to the target. -/
theorem normalizerCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (hv : InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S member)
    (ho : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old)
    (v : List.Vector Nat 1) :
    evaluate (normalizer validity member old) v =
      targetRepresentativeValue n arity symbols S Gamma (v.get 0) := by
  calc
    _ = evaluate (normalizer validity member old) (List.Vector.ofFn ![v.get 0]) :=
      congrArg (evaluate (normalizer validity member old)) (unaryVector v)
    _ = InternalApplicationResultFoldCalibration.semanticFold
        (fun x => evaluate (rootGuard validity member) (List.Vector.ofFn ![x]))
        (fun x => evaluate (InternalRepresentativeFoldCalibration.leaf validity member old)
          (List.Vector.ofFn ![x]))
        (fun d e f a => evaluate (combine old) (List.Vector.ofFn ![d,e,f,a])) (v.get 0) :=
      (InternalApplicationResultFoldCalibrationEvaluationProof.actualOriginalBoundedResultFoldCalibration
        (rootGuard validity member) (InternalRepresentativeFoldCalibration.leaf validity member old)
        (combine old) (v.get 0)).2
    _ = _ := actualOriginalSemanticRepresentativeFoldCalibration
      n arity symbols S Gamma table validity member old hc hv hm ho (v.get 0)

theorem sourceFromTarget (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat) :
    sourceRepresentativeValue n arity symbols S Gamma value =
      if sourceValidityValue n arity symbols S Gamma value = 1 then
        targetRepresentativeValue n arity symbols S Gamma value else 0 := by
  cases hd : NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceRepresentativeValue, sourceValidityValue,
      NumberedNumericCarrier.rawCarrierTest, hd]
  | some q =>
    have hp := (Option.filter_eq_some_iff.mp hd).1
    simp [sourceRepresentativeValue, sourceValidityValue,
      NumberedNumericCarrier.rawCarrierTest, targetRepresentativeValue, hd, hp]

theorem actualOriginalRepresentativeFoldProgramCalibration :
    InternalRepresentativeFoldCalibrationTargets.ActualOriginalRepresentativeFoldProgramCalibration := by
  intro n arity symbols S Gamma table validity member old hc hv hm ho
  refine ⟨ho.1,?_,?_⟩
  · intro v
    change evaluate (InternalAcceptance.branch
      (InternalApplicationValidityStack.exactOne (rootGuard validity member))
      (InternalAcceptance.constantZero 1) (normalizer validity member old)) v = _
    rw [evalBranch, exactOneEvaluation,
      rootGuardCalibration n arity symbols S Gamma validity member hv hm,
      zeroEvaluation, normalizerCalibration n arity symbols S Gamma table validity member old hc hv hm ho,
      sourceFromTarget]
    by_cases hs : sourceValidityValue n arity symbols S Gamma (v.get 0) = 1 <;> simp [hs]
  · exact normalizerCalibration n arity symbols S Gamma table validity member old hc hv hm ho

theorem actualOriginalFixedWindowRepresentativeSelection :
    InternalRepresentativeFoldCalibrationTargets.ActualOriginalFixedWindowRepresentativeSelection := by
  intro n arity symbols S Gamma table validity member old hv hm ho
  classical
  by_cases hc : SubtypeClosed (fun tau => tau ∈ S)
  · refine ⟨foldedData validity member old,
      actualOriginalRepresentativeFoldProgramCalibration
        n arity symbols S Gamma table validity member old hc hv hm ho,
      fun _ => rfl, ?_⟩
    exact fun h => False.elim (h hc)
  · exact ⟨old,ho,fun h => False.elim (hc h),fun _ => rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationProof
