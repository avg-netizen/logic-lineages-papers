import LogicLineages.PersistentMarking.NativeOrdinalRealizationTargets
import LogicLineages.PersistentMarking.NativeClosedStrictWellFoundedChecks
import LogicLineages.PersistentMarking.NativeClosedApplicationChecks
import LogicLineages.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.PersistentMarking.OrdinalRealizationClosureProof

namespace LogicLineages.PersistentMarking.NativeOrdinalRealizationProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeClosedApplication
open OrdinalRealizationTargets OrdinalRealizationClosureProof NativeOrdinalRealizationTargets

theorem shapes : ExactSemanticShapes := by
  constructor
  · intro A
    induction A with
    | base => rfl
    | arrow A D hA hD => simp only [nativeShape, valueShape, hA, hD]
  · intro A
    induction A with
    | base => rfl
    | arrow A D hA hD => simp only [nativeShape, valueShape, hA, hD]

theorem applicationEdge (S : Signature) : StrictFunctionSlot (nativeTerms S) := by
  intro A D s t u edge
  exact NativeClosedApplicationChecks.exact_NativeApplicationFunctionStrict S
    (actualType (nativeShape A)) (actualType (nativeShape D)) s t u edge

theorem exact_NativeRealizationClosure : NativeRealizationClosure := by
  refine ⟨shapes, exact_PointwiseSupremumExists, ?_⟩
  intro S
  let wf := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  exact ⟨wf, exact_RealizationStrictBackward (nativeTerms S) wf (applicationEdge S),
    exact_RealizationDownward (nativeTerms S) wf, exact_RealizationCountableSupremum (nativeTerms S) wf⟩

theorem exact_NativeLambdaRealization : NativeLambdaRealization := by
  intro S
  let wf := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  refine ⟨wf, ?_⟩
  intro A D body hl f bodyRealization x u hu
  let abstraction : (nativeTerms S).term (.arrow A D) := ⟨.lam (actualType (nativeShape A)) body, hl⟩
  let start := applyClosed abstraction u
  obtain ⟨result, resultValue, _, edge⟩ :=
    NativeClosedBetaChecks.exact_ClosedNativeBeta S (actualType (nativeShape A))
      (actualType (nativeShape D)) body hl u
  obtain ⟨claimed, claimedValue, hClaimed⟩ := bodyRealization x u hu
  have same : claimed = result := Subtype.ext (claimedValue.trans resultValue.symm)
  rw [same] at hClaimed
  exact exact_RealizationStrictBackward (nativeTerms S) wf (applicationEdge S)
    D start result (f x) edge hClaimed

#print axioms exact_NativeRealizationClosure
#print axioms exact_NativeLambdaRealization

end LogicLineages.PersistentMarking.NativeOrdinalRealizationProof
