module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyArgumentListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadGuardNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafTypeTest)
open NumberedWindowInternalCoverTypeOnlyArgumentListTargets

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem actualMember (s : Settings) (ty : Nat) :
    run (grammarTypeAt s) ty = 1 ↔ ty ∈ s.types := by
  let T := s.types
  let xs := ty ::ᵥ nil
  let calls : Fin 2 → Program 1 :=
    ![NumberedWindowInternalFreshProbeDispatchProgram.literal 1 (Encodable.encode T),.projection 0]
  change evaluate NumberedWindowInternalSparseScratchMembership.scratchMember
    (List.Vector.ofFn (fun i => evaluate (calls i) xs)) = 1 ↔ ty ∈ T
  rw [vectorTwo]
  change evaluate NumberedWindowInternalSparseScratchMembership.scratchMember
    (evaluate (NumberedWindowInternalFreshProbeDispatchProgram.literal 1 (Encodable.encode T)) xs ::ᵥ
      ty ::ᵥ nil) = 1 ↔ ty ∈ T
  rw [literalEvaluation,exact_AllInputScratchMembership,listCode,numbersRoundTrip]
  change (T.any (fun head => head == ty)).toNat = 1 ↔ ty ∈ T
  constructor
  · intro report
    have ok : T.any (fun head => head == ty) = true := by
      cases e : T.any (fun head => head == ty) <;> simp_all
    obtain ⟨x,hx,eq⟩ := List.any_eq_true.mp ok
    have same : x = ty := by simpa using eq
    exact same ▸ hx
  · intro member
    have hit : (T.any (fun head => head == ty)) = true :=
      List.any_eq_true.mpr ⟨ty,member,by simp⟩
    rw [hit] <;> rfl

private theorem firstValue {q ty : Nat} (read : unpackNode q = some (3,[ty])) :
    run (field 0) q = ty := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 3 (pack [ty]))).2
  have inner : run cellHead (pack [ty]) = ty := (headTailOfCell (cellAt ty (pack []))).1
  change run (field 0) (pair 3 (pack [ty])+1) = ty
  simp only [field,cursor,applyValue,outer,inner]

theorem exact_CoverTypeOnlyHeadGuardNumeric : ExactCoverTypeOnlyHeadGuardNumeric := by
  intro s raw
  have both : run (typeOnlyHeadGuard s) raw = 1 ↔
      run (header 3 1) raw = 1 ∧ run (leafTypeTest s) raw = 1 := by
    change evaluate (conjunction (header 3 1) (leafTypeTest s)) (raw ::ᵥ nil) = 1 ↔
      evaluate (header 3 1) (raw ::ᵥ nil) = 1 ∧ evaluate (leafTypeTest s) (raw ::ᵥ nil) = 1
    rw [actualConjunctionEvaluation]
    split <;> simp_all
  rw [both]
  constructor
  · intro ⟨head,approved⟩
    obtain ⟨fs,read,len⟩ := (exact_CoverHeaderUnpackNode 3 1 raw).mp head
    rcases fs with _ | ⟨ty,_ | ⟨_,_⟩⟩ <;> simp at len
    have tested : run (grammarTypeAt s) (run (field 0) raw) = 1 := approved
    rw [firstValue read] at tested
    exact ⟨ty,read,(actualMember s ty).mp tested⟩
  · intro ⟨ty,read,member⟩
    refine ⟨(exact_CoverHeaderUnpackNode 3 1 raw).mpr ⟨[ty],read,rfl⟩,?_⟩
    change run (grammarTypeAt s) (run (field 0) raw) = 1
    rw [firstValue read]
    exact (actualMember s ty).mpr member

#print axioms exact_CoverTypeOnlyHeadGuardNumeric

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadGuardNumericProof
