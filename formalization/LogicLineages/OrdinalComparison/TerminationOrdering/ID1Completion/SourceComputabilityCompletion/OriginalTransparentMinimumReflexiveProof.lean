module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTargetLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumReflexiveProof
open Source OriginalTransparentMinimum InternalOriginalUniformParameterLeaves
open InternalAcceptanceCalibrationProof InternalEqualityTestEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Reflexivity is built into the original growing reachable list. No universe
filter, closed window or structural coherence assumption is used. -/
theorem initialReachable {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (q : NumberedUniformPackedDecoding.RawPacked n) (fuel : Nat) :
    q ∈ ContextUniformPrimary.reachable arity symbols S Gamma q fuel := by
  induction fuel with
  | zero => exact List.mem_cons_self
  | succ fuel ih =>
    simp only [ContextUniformPrimary.reachable,Function.iterate_succ_apply'] at ih ⊢
    exact List.mem_append_left _ ih

theorem rawClassReflexive {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat) :
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma value).any
      (fun q => ContextUniformPrimary.classNumberTest arity symbols S Gamma q value)).toNat =
      (NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma value).isSome.toNat := by
  cases hd : NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma value with
  | none => rfl
  | some q =>
    simp only [Option.any_some,Option.isSome_some,ContextUniformPrimary.classNumberTest,hd,
      ContextUniformPrimary.primaryTest,ContextUniformPrimary.primaryList]
    simp only [initialReachable,decide_true]

theorem classReflexive (n : Nat) (arity : Fin n → Nat) (seed parameter : Nat) :
    classValue n arity (ofFn ![seed,seed,parameter]) =
      targetValue n arity (ofFn ![seed,parameter]) := by
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma parameter
  change decodedValue n (fun ctx obj =>
      ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).any
        (fun q => ContextUniformPrimary.classNumberTest arity ctx.1.1 ctx.1.2 obj.1 q seed)).toNat)
      seed parameter =
    decodedValue n (fun _ obj =>
      (NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).isSome.toNat)
      seed parameter
  simp only [decodedValue,ho seed]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair parameter).1 with
  | none => rfl
  | some ctx => exact rawClassReflexive arity ctx.1.1 ctx.1.2 Gamma seed

theorem reflexiveEvaluation (T : Program 2) (P : Program 3) (v : List.Vector Nat 3) :
    evaluate (reflexiveClassTest T P) v =
      if v.get 1 = v.get 0 then evaluate T (ofFn ![v.get 0,v.get 2]) else evaluate P v := by
  have he : evaluate (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0]) v =
      if v.get 1 = v.get 0 then 1 else 0 := by
    change evaluate InternalEqualityTest.equalityTest (ofFn ![v.get 1,v.get 0]) = _
    rw [vectorTwo]
    exact exactEqualityEvaluation _ _
  rw [reflexiveClassTest,evalBranch,he]
  by_cases h : v.get 1 = v.get 0 <;> simp [h,evaluate]

theorem actualOriginalTransparentMinimumReflexiveCalibration :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumReflexiveCalibration := by
  intro n arity H G P hH hG hP v
  rw [reflexiveEvaluation]
  split_ifs with he
  · rw [OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration
      n arity H G hH hG,hP]
    have hv : v = ofFn ![v.get 0,v.get 0,v.get 2] := by
      apply List.Vector.ext
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
      · rfl
      · exact he
      · rfl
    conv_rhs => rw [hv]
    exact (classReflexive n arity _ _).symm
  · rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumReflexiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumReflexiveProof
