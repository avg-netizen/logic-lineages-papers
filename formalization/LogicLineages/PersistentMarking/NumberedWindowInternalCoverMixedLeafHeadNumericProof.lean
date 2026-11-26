module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafArgumentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeOnlyHeadGuardNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafHeadNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization List.Vector
open InternalAcceptance (branch conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation evalBranch evalNormalize)
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
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue bothAccept)
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

open NumberedWindowInternalCoverTypeOnlyHeadGuardNumericProof (exact_CoverTypeOnlyHeadGuardNumeric)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalCoverMixedLeafArgumentTargets

private theorem firstValue {q tag ty i : Nat} (read : unpackNode q = some (tag,[ty,i])) :
    run (field 0) q = ty := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt tag (pack [ty,i]))).2
  have inner : run cellHead (pack [ty,i]) = ty := (headTailOfCell (cellAt ty (pack [i]))).1
  change run (field 0) (pair tag (pack [ty,i])+1) = ty
  simp only [field,cursor,applyValue,outer,inner]

private theorem namedGate (s : Settings) (b : Bool) (raw : Nat) :
    run (namedGrammarHead s b) raw = 1 ↔
      ∃ ty i, unpackNode raw = some (b.toNat,[ty,i]) ∧ ty ∈ s.types := by
  rw [namedGrammarHead,bothAccept]
  constructor
  · intro ⟨head,approved⟩
    obtain ⟨fs,read,len⟩ := (exact_CoverHeaderUnpackNode b.toNat 2 raw).mp head
    rcases fs with _ | ⟨ty,_ | ⟨i,_ | ⟨_,_⟩⟩⟩ <;> simp at len
    have tested : run (grammarTypeAt s) (run (field 0) raw) = 1 := approved
    rw [firstValue read] at tested
    exact ⟨ty,i,read,(actualMember s ty).mp tested⟩
  · intro ⟨ty,i,read,member⟩
    refine ⟨(exact_CoverHeaderUnpackNode b.toNat 2 raw).mpr ⟨[ty,i],read,rfl⟩,?_⟩
    change run (grammarTypeAt s) (run (field 0) raw) = 1
    rw [firstValue read]
    exact (actualMember s ty).mpr member

private theorem union (X Y : Program 1) (raw : Nat) :
    run (unionHeadGuard X Y) raw = 1 ↔ run X raw = 1 ∨ run Y raw = 1 := by
  change evaluate (branch (normalize X) (normalize Y) (literal 1 1)) (raw ::ᵥ nil) = 1 ↔
    evaluate X (raw ::ᵥ nil) = 1 ∨ evaluate Y (raw ::ᵥ nil) = 1
  rw [evalBranch,evalNormalize,evalNormalize,literalEvaluation]
  by_cases x : evaluate X (raw ::ᵥ nil) = 1 <;>
    by_cases y : evaluate Y (raw ::ᵥ nil) = 1 <;> simp [x,y]

theorem exact_CoverMixedLeafHeadNumeric : ExactCoverMixedLeafHeadNumeric := by
  intro s raw
  rw [mixedLeafHead,union,union,exact_CoverTypeOnlyHeadGuardNumeric,namedGate,namedGate]
  unfold OriginalMixedLeaf
  constructor
  · intro a
    rcases a with h | h | h
    · exact Or.inl h
    · obtain ⟨ty,i,read,member⟩ := h
      exact Or.inr ⟨false,ty,i,read,member⟩
    · obtain ⟨ty,i,read,member⟩ := h
      exact Or.inr ⟨true,ty,i,read,member⟩
  · intro a
    rcases a with h | ⟨b,ty,i,read,member⟩
    · exact Or.inl h
    · cases b
      · exact Or.inr (Or.inl ⟨ty,i,read,member⟩)
      · exact Or.inr (Or.inr ⟨ty,i,read,member⟩)

#print axioms exact_CoverMixedLeafHeadNumeric

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMixedLeafHeadNumericProof
