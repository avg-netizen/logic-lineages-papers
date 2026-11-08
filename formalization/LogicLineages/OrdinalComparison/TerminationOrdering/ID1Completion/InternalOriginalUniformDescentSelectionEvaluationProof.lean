module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionSemanticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
open Source InternalOriginalUniformDescentSelection InternalOriginalUniformDescentSelectionTargets
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalOriginalUniformParameterLeavesCodecProof InternalOriginalUniformParameterLeavesCalibrationProof
open InternalCanonicalDescentSelectionSemanticSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Specialize the SAME four globally calibrated leaves, never select new
unary witnesses after the window or Gamma has been supplied. -/
theorem leafSlice (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (value : Nat) :
    evaluate data.oldSource (ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value ∧
    evaluate data.oldTarget (ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value ∧
    evaluate data.oldRepresentative (ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value ∧
    evaluate data.member (ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalStructuralEndpointGuard.membershipValue S value := by
  let v := ofFn ![value,parameterCode symbols S Gamma table]
  have hs := actualOriginalUniformLeafCalibration n arity v
  change evaluate data.oldSource v = _ ∧ evaluate data.oldTarget v = _ ∧
    evaluate data.oldRepresentative v = _ ∧ evaluate data.member v = _
  rw [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2]
  simp only [v,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    decodedValueAtParameter,and_self]

theorem actualOriginalUniformValidityCalibration : ActualOriginalUniformValidityCalibration := by
  intro n arity data hc symbols S Gamma table value
  have hs := leafSlice n arity data hc symbols S Gamma table
  have h := InternalParameterizedApplicationValidityFoldCalibrationProof.actualOriginalParameterizedValidityFoldCalibration
    n arity symbols S Gamma data.oldSource data.oldTarget data.member
    (parameterCode symbols S Gamma table)
    (fun x => (hs x).1) (fun x => (hs x).2.1) (fun x => (hs x).2.2.2) value
  exact ⟨h.1,h.2.2⟩

theorem transitionEvaluation (R V : Program 2) (value parameter : Nat) :
    evaluate (InternalParameterizedBoundedDescentNormalizer.transition R V) (ofFn ![value,parameter]) =
      if evaluate R (ofFn ![value,parameter]) < value ∧
          evaluate V (ofFn ![evaluate R (ofFn ![value,parameter]),parameter]) = 1 ∧
          (Nat.unpair (evaluate R (ofFn ![value,parameter]))).1 = (Nat.unpair value).1
      then evaluate R (ofFn ![value,parameter]) else value := by
  let r := evaluate R (ofFn ![value,parameter])
  have hl : evaluate InternalParameterizedBoundedDescentNormalizer.candidateLess
      (ofFn ![r,value,parameter]) = if r < value then 1 else 0 := by
    change evaluate InternalLessThan.ltTest (ofFn ![r,value]) = _
    simpa only [vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one] using
      InternalLessThanEvaluationProof.exactLessThanEvaluation r value
  have hv : evaluate (InternalParameterizedBoundedDescentNormalizer.candidateValid V)
      (ofFn ![r,value,parameter]) = evaluate V (ofFn ![r,parameter]) := rfl
  have ht : evaluate InternalParameterizedBoundedDescentNormalizer.sameLeft
      (ofFn ![r,value,parameter]) =
        if (Nat.unpair r).1 = (Nat.unpair value).1 then 1 else 0 := by
    change evaluate (InternalApplicationStepPeel.same
      (leftOf (.projection 0)) (leftOf (.projection 1))) (ofFn ![r,value,parameter]) = _
    rw [sameEvaluation,leftOfEvaluation,leftOfEvaluation]
    rfl
  change evaluate (InternalParameterizedBoundedDescentNormalizer.choose V)
    (ofFn ![r,value,parameter]) = _
  rw [InternalParameterizedBoundedDescentNormalizer.choose,evalBranch,
    InternalParameterizedBoundedDescentNormalizer.guard,conjunctionEvaluation,conjunctionEvaluation,hl,hv,ht]
  change (if (if (if r < value then 1 else 0) = 1 ∧
    (if evaluate V (ofFn ![r,parameter]) = 1 ∧
      (if (Nat.unpair r).1 = (Nat.unpair value).1 then 1 else 0) = 1
      then 1 else 0) = 1 then 1 else 0) = 0 then value else r) = _
  change _ = if r < value ∧ evaluate V (ofFn ![r,parameter]) = 1 ∧
    (Nat.unpair r).1 = (Nat.unpair value).1 then r else value
  split_ifs <;> simp_all

theorem actualOriginalUniformTransitionIdentification : ActualOriginalUniformTransitionIdentification := by
  intro n arity data hc symbols S Gamma table hS value hv
  have hr := leafSlice n arity data hc symbols S Gamma table
  have hvalid := actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table
  have hf := representativeFacts n arity symbols S Gamma hS value hv
  dsimp only at hf
  rw [transitionEvaluation,(hr value).2.2.1,(hvalid _).2]
  by_cases hlt : InternalQuotientEdgeChecker.targetRepresentativeValue
      n arity symbols S Gamma value < value
  · simp only [hlt,hf.2.1,hf.2.2.1,and_self,ite_true]
  · have heq : InternalQuotientEdgeChecker.targetRepresentativeValue
        n arity symbols S Gamma value = value :=
      Nat.le_antisymm hf.1 (Nat.le_of_not_gt hlt)
    simp only [heq,ite_self]

theorem normalizerEvaluation (R V : Program 2) (value parameter : Nat) :
    evaluate (InternalParameterizedBoundedDescentNormalizer.normalizer R V) (ofFn ![value,parameter]) =
      (fun x => evaluate (InternalParameterizedBoundedDescentNormalizer.transition R V)
        (ofFn ![x,parameter]))^[value+1] value := by
  change evaluate (InternalParameterizedNumericIteration.repeatP
    (InternalParameterizedBoundedDescentNormalizer.transition R V)) (ofFn ![value+1,value,parameter]) = _
  simpa only [vectorThree,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_succ] using
      InternalParameterizedNumericIterationEvaluationProof.exactParameterizedNumericIterationEvaluation
        (InternalParameterizedBoundedDescentNormalizer.transition R V) (value+1) value parameter

theorem normalizerCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat)
    (hv : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate (InternalParameterizedBoundedDescentNormalizer.normalizer data.oldRepresentative (validity data))
      (ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value := by
  let r := InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value
  let t := fun x => evaluate (InternalParameterizedBoundedDescentNormalizer.transition
    data.oldRepresentative (validity data)) (ofFn ![x,parameterCode symbols S Gamma table])
  have hf := representativeFacts n arity symbols S Gamma hS value hv
  have hfirst : t value = r := actualOriginalUniformTransitionIdentification
    n arity data hc symbols S Gamma table hS value hv
  have hfixed : t r = r := (actualOriginalUniformTransitionIdentification
    n arity data hc symbols S Gamma table hS r hf.2.1).trans hf.2.2.2
  have hi (k : Nat) : t^[k+1] value = r := by
    induction k with
    | zero => simpa using hfirst
    | succ k ih => rw [Function.iterate_succ_apply',ih,hfixed]
  rw [normalizerEvaluation]
  exact hi value

theorem fallbackEvaluation (R V : Program 2) (value parameter : Nat) :
    evaluate (fallbackRepresentative R V) (ofFn ![value,parameter]) =
      if evaluate V (ofFn ![value,parameter]) = 1 then
        evaluate (InternalParameterizedBoundedDescentNormalizer.normalizer R V) (ofFn ![value,parameter])
      else evaluate R (ofFn ![value,parameter]) := by
  rw [fallbackRepresentative,evalBranch,exactOneEvaluation]
  by_cases h : evaluate V (ofFn ![value,parameter]) = 1 <;> simp_all

theorem actualOriginalUniformRepresentativeCalibration : ActualOriginalUniformRepresentativeCalibration := by
  intro n arity data hc symbols S Gamma table hS value
  change evaluate (fallbackRepresentative _ _) _ = _
  rw [fallbackEvaluation,(actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table value).2]
  split_ifs with hv
  · exact normalizerCalibration n arity data hc symbols S Gamma table hS value hv
  · exact (leafSlice n arity data hc symbols S Gamma table value).2.2.1

theorem typedEvaluation (R V member : Program 2) (value typ parameter : Nat) :
    evaluate (typedChecker R V member) (ofFn ![value,typ,parameter]) =
      if evaluate member (ofFn ![typ,parameter]) = 1 ∧
          evaluate V (ofFn ![value,parameter]) = 1 ∧
          (Nat.unpair value).1 = typ ∧
          evaluate (InternalParameterizedBoundedDescentNormalizer.transition R V)
            (ofFn ![value,parameter]) = value then 1 else 0 := by
  have ht : evaluate sameOuterType (ofFn ![value,typ,parameter]) =
      if (Nat.unpair value).1 = typ then 1 else 0 := by
    rw [sameOuterType,sameEvaluation,leftOfEvaluation]
    rfl
  rw [typedChecker,conjunctionEvaluation,conjunctionEvaluation,conjunctionEvaluation,
    ht,transitionFixed,sameEvaluation]
  change (if evaluate member (ofFn ![typ,parameter]) = 1 ∧
    (if evaluate V (ofFn ![value,parameter]) = 1 ∧
      (if (if (Nat.unpair value).1 = typ then 1 else 0) = 1 ∧
        (if evaluate (InternalParameterizedBoundedDescentNormalizer.transition R V)
          (ofFn ![value,parameter]) = value then 1 else 0) = 1 then 1 else 0) = 1
      then 1 else 0) = 1 then 1 else 0) = _
  split_ifs <;> simp_all

theorem actualOriginalUniformTypedCalibration : ActualOriginalUniformTypedCalibration := by
  intro n arity data hc symbols S Gamma table hS value typ
  change evaluate (typedChecker _ _ _) _ = _
  rw [typedEvaluation,(leafSlice n arity data hc symbols S Gamma table typ).2.2.2,
    (actualOriginalUniformValidityCalibration n arity data hc symbols S Gamma table value).2]
  by_cases hv : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value = 1
  · rw [actualOriginalUniformTransitionIdentification n arity data hc symbols S Gamma table hS value hv]
    have ht := typedCharacterization n arity symbols S Gamma (ofFn ![value,typ])
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one] at ht
    by_cases hh : (Nat.unpair value).1 = typ ∧
        InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value = value
    · have ho : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma (ofFn ![value,typ]) = 1 := by
        simpa only [hv,hh.1,hh.2,and_self,ite_true] using ht
      have hm := InternalTypedEdgePresentationEvaluationProof.originalAcceptanceMembership
        n arity symbols S Gamma (ofFn ![value,typ]) ho
      simp only [List.Vector.get_ofFn,Matrix.cons_val_one,Matrix.cons_val_zero] at hm
      simp only [hv,hh.1,hh.2,hm,ho,and_self,ite_true]
    · rw [ht]
      simp only [hv,hh,and_false,ite_false]
  · rw [typedCharacterization]
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,hv,false_and,and_false,ite_false]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
