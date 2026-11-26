module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem flattenStepValue (D : Program 2) (node param : Nat) (deps rest : List Nat)
    (hd : evaluate D (ofFn ![node,param]) = numbersNumber deps) :
    evaluate (flattenStep D) (node ::ᵥ numbersNumber rest ::ᵥ param ::ᵥ nil) =
      numbersNumber (deps ++ rest) := by
  change evaluate InternalApplicationValidityStackAppend.append
    (ofFn ![evaluate D (ofFn ![node,param]),numbersNumber rest]) = _
  rw [hd,PrimaryExpansion.NativeProof.appendEvaluation,numbersRoundTrip]
  rfl

theorem flattenFold (D : Program 2) (d : Nat → Nat → List Nat)
    (hd : ∀ node param, evaluate D (ofFn ![node,param]) = numbersNumber (d node param))
    (nodes : List Nat) (param : Nat) :
    nodes.foldr (fun node rest => evaluate (flattenStep D) (node ::ᵥ rest ::ᵥ param ::ᵥ nil)) 0 =
      numbersNumber (nodes.flatMap (fun node => d node param)) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    rw [List.foldr_cons,ih,flattenStepValue D node param _ _ (hd node param),List.flatMap_cons]

theorem nativeFlatten : Targets.NativeFlatten := by
  intro D d hd nodes param
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (InternalAcceptance.constantZero 1) (flattenStep D) (param ::ᵥ nil) (numbersNumber nodes)
  change evaluate (flatten D) (ofFn ![numbersNumber nodes,param]) = _ at h
  rw [h,numbersRoundTrip]
  exact flattenFold D d hd nodes param

theorem bindZero (D : Program 2) (seed param : Nat) :
    evaluate (bindList D) (ofFn ![0,seed,param]) = numbersNumber [seed] := by
  change evaluate InternalListCodec.consCode (ofFn ![seed,0]) = _
  rw [InternalEqualityTestEvaluationProof.vectorTwo,InternalListCodecEvaluationProof.consEvaluation]
  rfl

theorem bindSuccessor (D : Program 2) (depth seed param : Nat) :
    evaluate (bindList D) (ofFn ![depth+1,seed,param]) =
      evaluate (flatten D) (ofFn ![evaluate (bindList D) (ofFn ![depth,seed,param]),param]) := rfl

theorem nativeBindList : Targets.NativeBindList := by
  intro D d hd depth seed param
  induction depth with
  | zero => exact bindZero D seed param
  | succ depth ih =>
    rw [bindSuccessor,ih,nativeFlatten D d hd]
    rfl

theorem originalRankBound (n : Nat) (source target : NumberedAuxiliaryCoding.Code (Fin n))
    (depth : Nat) (x y : NumberedAuxiliaryCoding.Code (Fin n))
    (h : (x,y) ∈ originalFrontier source target depth) :
    NumberedLeastCodeRepresentative.codeNumber x + depth ≤ NumberedLeastCodeRepresentative.codeNumber source := by
  induction depth generalizing x y with
  | zero =>
    simp only [originalFrontier,List.mem_singleton] at h
    cases h
    exact Nat.le_refl _
  | succ depth ih =>
    obtain ⟨⟨a,b⟩,hab,hxy⟩ := List.mem_flatMap.mp h
    have ha := ih a b hab
    have hx := (ExchangeRowMemo.NativeProof.originalDependencyBounds n a b x y hxy).1
    omega

theorem originalRankExhaustion : Targets.OriginalRankExhaustion := by
  intro n source target
  refine ⟨originalRankBound n source target, ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro xy h
  have hb := originalRankBound n source target _ xy.1 xy.2 h
  omega
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.NativeProof
