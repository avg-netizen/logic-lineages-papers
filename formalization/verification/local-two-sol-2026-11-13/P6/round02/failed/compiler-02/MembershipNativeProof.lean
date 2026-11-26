module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
open Source Membership NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalOriginalUniformParameterLeaves OriginalTransparentMinimum
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof

theorem stepEvaluation (head rest needle : Nat) :
    evaluate containsStep (head ::ᵥ rest ::ᵥ needle ::ᵥ nil) =
      if head = needle then 1 else rest := by
  rw [containsStep,evalBranch]
  have he : evaluate (.composition InternalEqualityTest.equalityTest
      ![.projection 0,.projection 2]) (head ::ᵥ rest ::ᵥ needle ::ᵥ nil) =
      if head = needle then 1 else 0 := by
    change evaluate InternalEqualityTest.equalityTest (ofFn ![head,needle]) = _
    rw [vectorTwo]
    exact exactEqualityEvaluation head needle
  rw [he]
  by_cases h : head = needle <;> simp [h,InternalLessThan.constantOne,evaluate]

theorem foldEvaluation (xs : List Nat) (needle : Nat) :
    xs.foldr (fun head rest => evaluate containsStep (head ::ᵥ rest ::ᵥ needle ::ᵥ nil)) 0 =
      (decide (needle ∈ xs)).toNat := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldr_cons,ih,stepEvaluation]
    by_cases h : head = needle <;> simp [h,eq_comm]

theorem actualContainsNative : MembershipTargets.ActualContainsNative := by
  intro code needle
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (InternalAcceptance.constantZero 1) containsStep (needle ::ᵥ nil) code
  change evaluate contains (ofFn ![code,needle]) = _ at h
  rw [h]
  exact foldEvaluation _ needle

theorem classEvaluation (T L D : Program 2) (seed candidate parameter : Nat) :
    evaluate (classTest T L D) (ofFn ![seed,candidate,parameter]) =
      if evaluate T (ofFn ![candidate,parameter]) = 1 then
        (decide (evaluate D (ofFn ![candidate,parameter]) ∈
          (decodeNumbers (evaluate L (ofFn ![seed,parameter]))).getD [])).toNat
      else 0 := by
  rw [classTest,actualConjunctionEvaluation]
  change (if evaluate T (ofFn ![candidate,parameter]) = 1 then
      if evaluate contains (ofFn ![evaluate L (ofFn ![seed,parameter]),
        evaluate D (ofFn ![candidate,parameter])]) = 1 then 1 else 0 else 0) = _
  rw [actualContainsNative]
  by_cases ht : evaluate T (ofFn ![candidate,parameter]) = 1
  · simp only [ht,ite_true]
    cases decide (evaluate D (ofFn ![candidate,parameter]) ∈
      (decodeNumbers (evaluate L (ofFn ![seed,parameter]))).getD []) <;> rfl
  · simp [ht]

theorem encodedMembership {n : Nat} (q : NumberedUniformPackedDecoding.RawPacked n)
    (xs : List (NumberedUniformPackedDecoding.RawPacked n)) :
    Encodable.encode q ∈ xs.map Encodable.encode ↔ q ∈ xs := by
  constructor
  · intro h
    obtain ⟨r,hr,he⟩ := List.mem_map.mp h
    have heq := Encodable.encode_injective he
    cases heq
    exact hr
  · intro h
    exact List.mem_map.mpr ⟨q,h,rfl⟩

theorem actualClassCalibration : MembershipTargets.ActualClassCalibration := by
  intro n arity T L D hT hL hD v
  have atInput (seed candidate parameter : Nat) :
      evaluate (classTest T L D) (ofFn ![seed,candidate,parameter]) =
        classValue n arity (ofFn ![seed,candidate,parameter]) := by
    rw [classEvaluation,hT,hL,hD]
    obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma parameter
    simp only [targetValue,listValue,candidateValue,classValue,List.Vector.get_ofFn,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,decodedValue,ho seed,ho candidate]
    cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1 with
    | none => simp [hc]
    | some ctx =>
      simp only [hc]
      cases hs : NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed with
      | none => simp [hs]
      | some q =>
        cases hr : NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma candidate with
        | none => simp [hr,hs,ContextUniformPrimary.classNumberTest]
        | some r =>
          simp only [hs,hr,Option.map_some,Option.getD_some,Option.isSome_some,
            Bool.toNat_true,ite_true,entriesCode,numbersRoundTrip,Option.getD_some,
            ContextUniformPrimary.classNumberTest,hr,Option.any_some,ContextUniformPrimary.primaryTest]
          rw [encodedMembership]
  have hv : v = ofFn ![v.get 0,v.get 1,v.get 2] := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i <;> rfl
  simpa only [← hv] using atInput (v.get 0) (v.get 1) (v.get 2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
