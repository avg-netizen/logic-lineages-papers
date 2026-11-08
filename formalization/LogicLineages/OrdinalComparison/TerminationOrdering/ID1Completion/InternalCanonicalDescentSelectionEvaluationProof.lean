module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionSemanticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionEvaluationProof
open Source NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative
open InternalCanonicalDescentSelection
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open InternalCanonicalDescentSelectionSemanticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

 theorem sameLeftEvaluation (v : List.Vector Nat 2) :
    evaluate InternalBoundedDescentNormalizer.sameLeft v =
      if (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 then 1 else 0 := by
  change evaluate (InternalApplicationStepPeel.same
    (leftOf (.projection 0)) (leftOf (.projection 1))) v = _
  rw [sameEvaluation,leftOfEvaluation,leftOfEvaluation]
  rfl

 theorem transitionEvaluation (r valid : Program 1) (x : Nat) :
    evaluate (InternalBoundedDescentNormalizer.transition r valid) (ofFn ![x]) =
      if evaluate r (ofFn ![x]) < x ∧
          evaluate valid (ofFn ![evaluate r (ofFn ![x])]) = 1 ∧
          (Nat.unpair (evaluate r (ofFn ![x]))).1 = (Nat.unpair x).1
      then evaluate r (ofFn ![x]) else x := by
  change evaluate (InternalBoundedDescentNormalizer.choose valid)
    (ofFn ![evaluate r (ofFn ![x]),x]) = _
  rw [InternalBoundedDescentNormalizer.choose,evalBranch,
    InternalBoundedDescentNormalizer.guard,conjunctionEvaluation,conjunctionEvaluation,
    sameLeftEvaluation]
  have hl := InternalLessThanEvaluationProof.exactLessThanEvaluation
    (evaluate r (ofFn ![x])) x
  have hl' : evaluate InternalLessThan.ltTest (ofFn ![evaluate r (ofFn ![x]),x]) =
      if evaluate r (ofFn ![x]) < x then 1 else 0 := by
    simpa only [vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one] using hl
  rw [hl']
  change (if (if (if evaluate r (ofFn ![x]) < x then 1 else 0) = 1 ∧
      (if evaluate valid (ofFn ![evaluate r (ofFn ![x])]) = 1 ∧
        (if (Nat.unpair (evaluate r (ofFn ![x]))).1 = (Nat.unpair x).1
          then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0) = 0
      then x else evaluate r (ofFn ![x])) = _
  split_ifs <;> simp_all <;> omega

 theorem recursiveValidityCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : Data) (h : Calibrated n arity symbols S Gamma table data) :
    InternalOriginalStepGuard.Calibrated n arity symbols S Gamma (validity data) :=
  InternalApplicationValidityCalibrationProof.actualOriginalRecursiveValidityCalibration
    n arity symbols S Gamma data.oldValidity data.member h.1 h.2.1

 theorem actualOriginalCanonicalTransitionIdentification :
    InternalCanonicalDescentSelectionTargets.ActualOriginalCanonicalTransitionIdentification := by
  intro n arity symbols S Gamma table data hc h x hx
  have hv := recursiveValidityCalibration n arity symbols S Gamma table data h
  have hr := h.2.2.2.2
  have hf := representativeFacts n arity symbols S Gamma hc x hx
  dsimp only at hf
  have he : evaluate (InternalBoundedDescentNormalizer.transition
      data.oldEdge.targetRepresentative (validity data).sourceValid) (ofFn ![x]) =
      evaluate data.oldEdge.targetRepresentative (ofFn ![x]) := by
    rw [transitionEvaluation,hr,hv.1]
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
    by_cases hl : InternalQuotientEdgeChecker.targetRepresentativeValue
        n arity symbols S Gamma x < x
    · simp [hl,hf.2.1,hf.2.2.1]
    · have heq : InternalQuotientEdgeChecker.targetRepresentativeValue
          n arity symbols S Gamma x = x := Nat.le_antisymm hf.1 (Nat.le_of_not_gt hl)
      simp [hl,heq]
  exact ⟨he,by rw [he]⟩

 theorem repeatEvaluation (t : Program 1) (k x : Nat) :
    evaluate (InternalNumericIteration.repeatProgram t) (ofFn ![k,x]) =
      (fun y => evaluate t (ofFn ![y]))^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change evaluate t (ofFn ![evaluate (InternalNumericIteration.repeatProgram t)
      (ofFn ![k,x])]) = _
    rw [ih,Function.iterate_succ_apply']

 theorem normalizerCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : Calibrated n arity symbols S Gamma table data) (x : Nat)
    (hx : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma x = 1) :
    evaluate (InternalBoundedDescentNormalizer.normalizer data.oldEdge.targetRepresentative
      (validity data).sourceValid) (ofFn ![x]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma x := by
  let r := InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma x
  let t := fun y => evaluate (InternalBoundedDescentNormalizer.transition
    data.oldEdge.targetRepresentative (validity data).sourceValid) (ofFn ![y])
  have hf := representativeFacts n arity symbols S Gamma hc x hx
  have htx : t x = r := (actualOriginalCanonicalTransitionIdentification
    n arity symbols S Gamma table data hc h x hx).1.trans (h.2.2.2.2 _)
  have htr : t r = r := ((actualOriginalCanonicalTransitionIdentification
    n arity symbols S Gamma table data hc h r hf.2.1).1.trans
      (h.2.2.2.2 _)).trans hf.2.2.2
  have hi (k : Nat) : t^[k+1] x = r := by
    induction k with
    | zero => simpa using htx
    | succ k ih => rw [Function.iterate_succ_apply',ih,htr]
  change evaluate (InternalNumericIteration.repeatProgram
    (InternalBoundedDescentNormalizer.transition data.oldEdge.targetRepresentative
      (validity data).sourceValid)) (ofFn ![x+1,x]) = _
  rw [repeatEvaluation]
  exact hi x

 theorem fallbackEvaluation (r valid : Program 1) (v : List.Vector Nat 1) :
    evaluate (fallbackRepresentative r valid) v =
      if evaluate valid v = 1 then
        evaluate (InternalBoundedDescentNormalizer.normalizer r valid) v else evaluate r v := by
  rw [fallbackRepresentative,evalBranch,exactOneEvaluation]
  by_cases h : evaluate valid v = 1 <;> simp [h]

 theorem actualOriginalCanonicalDescentCalibration :
    InternalCanonicalDescentSelectionTargets.ActualOriginalCanonicalDescentCalibration := by
  intro n arity symbols S Gamma table data hc h v
  have hv := recursiveValidityCalibration n arity symbols S Gamma table data h
  rw [representative,fallbackEvaluation,hv.1]
  split_ifs with hx
  · have he : v = ofFn ![v.get 0] := by
      apply List.Vector.ext
      intro i
      obtain rfl := Fin.eq_zero i
      rfl
    conv_lhs => rw [he]
    exact normalizerCalibration n arity symbols S Gamma table data hc h (v.get 0) hx
  · exact h.2.2.2.2 v

 theorem typedEvaluation (r valid member : Program 1) (v : List.Vector Nat 2) :
    evaluate (typedChecker r valid member) v =
      if evaluate member (ofFn ![v.get 1]) = 1 ∧
          evaluate valid (ofFn ![v.get 0]) = 1 ∧
          (Nat.unpair (v.get 0)).1 = v.get 1 ∧
          evaluate (InternalBoundedDescentNormalizer.transition r valid)
            (ofFn ![v.get 0]) = v.get 0 then 1 else 0 := by
  rw [typedChecker,conjunctionEvaluation,typedCore,conjunctionEvaluation,
    conjunctionEvaluation,InternalOriginalTypedCarrierEvaluationProof.sameOuterTypeEvaluation,
    transitionFixed,sameEvaluation]
  change (if evaluate member (ofFn ![v.get 1]) = 1 ∧
    (if evaluate valid (ofFn ![v.get 0]) = 1 ∧
      (if (if (Nat.unpair (v.get 0)).1 = v.get 1 then 1 else 0) = 1 ∧
        (if evaluate (InternalBoundedDescentNormalizer.transition r valid)
          (ofFn ![v.get 0]) = v.get 0 then 1 else 0) = 1
        then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0) = _
  split_ifs <;> simp_all

 theorem actualOriginalCanonicalDescentTypedCalibration :
    InternalCanonicalDescentSelectionTargets.ActualOriginalCanonicalDescentTypedCalibration := by
  intro n arity symbols S Gamma table data hc h v
  have hv := recursiveValidityCalibration n arity symbols S Gamma table data h
  change evaluate (typedChecker _ _ _) v = _
  rw [typedEvaluation,h.2.1,hv.1]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
  by_cases hs : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 0) = 1
  · rw [(actualOriginalCanonicalTransitionIdentification
      n arity symbols S Gamma table data hc h (v.get 0) hs).1,h.2.2.2.2]
    simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
    have ht := typedCharacterization n arity symbols S Gamma v
    by_cases hh : (Nat.unpair (v.get 0)).1 = v.get 1 ∧
        InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma (v.get 0) = v.get 0
    · have ho : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 1 := by
        simpa only [hs,hh.1,hh.2,and_self,ite_true] using ht
      have hm := InternalTypedEdgePresentationEvaluationProof.originalAcceptanceMembership
        n arity symbols S Gamma v ho
      simp only [hs,hh.1,hh.2,hm,ho,and_self,ite_true]
    · rw [ht]
      simp only [hs,true_and,hh,and_false,ite_false]
  · rw [typedCharacterization]
    simp only [hs,false_and,and_false,ite_false]

 theorem actualOriginalCanonicalDescentDataCalibration :
    InternalCanonicalDescentSelectionTargets.ActualOriginalCanonicalDescentDataCalibration := by
  intro n arity symbols S Gamma table data hc h
  have hv := recursiveValidityCalibration n arity symbols S Gamma table data h
  have hr := actualOriginalCanonicalDescentCalibration n arity symbols S Gamma table data hc h
  refine ⟨hv,⟨h.2.2.1,?_,hr⟩,
    actualOriginalCanonicalDescentTypedCalibration n arity symbols S Gamma table data hc h⟩
  intro v
  change evaluate (InternalAcceptance.branch _ _ _) v = _
  rw [evalBranch,exactOneEvaluation,hv.1,hr]
  cases hd : decodeUniverse n arity symbols S Gamma (v.get 0) with
  | none =>
    simp only [InternalOriginalStepGuard.sourceValidityValue,rawCarrierTest,hd,
      InternalQuotientEdgeChecker.sourceRepresentativeValue,Option.isSome_none,Bool.toNat_false,
      Nat.zero_ne_one,ite_false,ite_true]
    rfl
  | some q => simp only [InternalOriginalStepGuard.sourceValidityValue,rawCarrierTest,hd,
      InternalQuotientEdgeChecker.sourceRepresentativeValue,Option.isSome_some,Bool.toNat_true,
      ite_true,Nat.one_ne_zero,ite_false,
      InternalQuotientEdgeChecker.targetRepresentativeValue,(Option.filter_eq_some_iff.mp hd).1]

 theorem calibratedDataExists (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    ∃ data : Data, Calibrated n arity symbols S Gamma table data := by
  obtain ⟨oldValidity,hv⟩ := InternalOriginalStepGuardProof.actualOriginalValidityProgramsExist
    n arity symbols S Gamma
  obtain ⟨member,hm⟩ := InternalStructuralEndpointGuardProof.actualOriginalMembershipProgramExists S
  obtain ⟨oldEdge,he⟩ := InternalQuotientEdgeCheckerEvaluationProof.actualOriginalProgramsExist
    n arity symbols S Gamma table
  exact ⟨⟨oldValidity,member,oldEdge⟩,hv,hm,he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionEvaluationProof
