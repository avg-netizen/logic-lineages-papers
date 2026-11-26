module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSettingsGrammarGuardDefinitions
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem memberOne (s : Settings) (ty : Nat)
    (member : ty ∈ s.types) :
    evaluate (grammarTypeAt s) (ty ::ᵥ nil) = 1 := by
  let T := s.types
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

theorem exact_SettingsRefitGuardCalibration : ExactSettingsRefitGuardCalibration := by
  intro s T included original ty
  change evaluate (refitGuard s T) (ty ::ᵥ nil) = (typeGuard s ty).toNat
  have originalValue : evaluate T (ty ::ᵥ nil) = (typeGuard s ty).toNat := original ty
  rw [refitGuard,actualConjunctionEvaluation,originalValue]
  cases h : typeGuard s ty
  · simp [h]
  · have listed : s.window.1.contains ty = true := (Bool.and_eq_true_iff.mp h).2
    have present : ty ∈ s.types := included ty (List.contains_iff_mem.mp listed)
    simp [h,memberOne s ty present]

#print axioms exact_SettingsRefitGuardCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericProof
