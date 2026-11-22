module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardTargets
import LogicLineages.PersistentMarking.NumberedWindowFixedGrammarTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber numbersRoundTrip)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalFixedGrammarGuardTargets

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem memberOne (S : Spine.Signature) (K : List Ty) (ty : Nat)
    (member : ty ∈ (fixed S K).types) :
    evaluate (grammarTypeAt S K) (ty ::ᵥ nil) = 1 := by
  let T := (fixed S K).types
  let xs := ty ::ᵥ nil
  let calls : Fin 2 → Program 1 :=
    ![NumberedWindowInternalFreshProbeDispatchProgram.literal 1 (Encodable.encode T),.projection 0]
  change evaluate NumberedWindowInternalSparseScratchMembership.scratchMember
    (List.Vector.ofFn (fun i => evaluate (calls i) xs)) = 1
  rw [vectorTwo]
  change evaluate NumberedWindowInternalSparseScratchMembership.scratchMember
    (evaluate (NumberedWindowInternalFreshProbeDispatchProgram.literal 1 (Encodable.encode T)) xs ::ᵥ
      ty ::ᵥ nil) = 1
  rw [literalEvaluation, exact_AllInputScratchMembership, listCode, numbersRoundTrip]
  have hit : (T.any (fun head => head == ty)) = true :=
    List.any_eq_true.mpr ⟨ty,member,by simp⟩
  change (T.any (fun head => head == ty)).toNat = 1
  rw [hit] <;> rfl

theorem calibration : ExactRefitGuardCalibration := by
  intro S K T original ty
  change evaluate (refitGuard S K T) (ty ::ᵥ nil) = (typeGuard (fixed S K) ty).toNat
  have originalValue : evaluate T (ty ::ᵥ nil) = (typeGuard (fixed S K) ty).toNat := original ty
  rw [refitGuard,actualConjunctionEvaluation,originalValue]
  cases h : typeGuard (fixed S K) ty
  · simp [h]
  · have accepted : run T ty = 1 := by
      rw [original ty,h] <;> rfl
    have present := NumberedWindowFixedGrammarType.guardRun S K T original ty accepted
    simp [h,memberOne S K ty present]

end LogicLineages.PersistentMarking.NumberedWindowInternalFixedGrammarGuardNumericProof
