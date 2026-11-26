module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeAdmissionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowNumericProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open InternalAcceptance (constantZero conjunction)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize evalZeroTest actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail cellGood chosenCell)
open NumberedWindowInternalSparsePathEnvelope (run field cursor applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell codeOfCell)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverLambdaLexicalWindowNumericProof (exact_CoverLambdaLexicalWindow)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets (singletonTypeGuard)
open NumberedWindowInternalCoverSingletonTypeAdmissionProof (exact_CoverOrdinarySingletonSourceType)
open NumberedWindowInternalCoverSingletonTypeWindowTargets

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem memberOne (s : Settings) (ty : Nat) (member : ty ∈ s.types) : run (grammarTypeAt s) ty = 1 := by
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
  rw [literalEvaluation,exact_AllInputScratchMembership,listCode,numbersRoundTrip]
  have hit : (T.any (fun head => head == ty)) = true :=
    List.any_eq_true.mpr ⟨ty,member,by simp⟩
  change (T.any (fun head => head == ty)).toNat = 1
  rw [hit] <;> rfl

private theorem sourceFirst {q ty : Nat} (read : unpackNode q = some (3,[ty])) :
    run (field 0) q = ty := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 3 (pack [ty]))).2
  have inner : run cellHead (pack [ty]) = ty := (headTailOfCell (cellAt ty (pack []))).1
  change run (field 0) (pair 3 (pack [ty])+1) = ty
  simp only [field,cursor,applyValue,outer,inner]

private theorem sourceSecond {raw h a : Nat} (read : unpackNode raw = some (4,[h,a])) :
    run (field 1) raw = a := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 4 (pack [h,a]))).2
  have middle : run cellTail (pack [h,a]) = pack [a] := (headTailOfCell (cellAt h (pack [a]))).2
  have inner : run cellHead (pack [a]) = a := (headTailOfCell (cellAt a (pack []))).1
  change run (field 1) (pair 4 (pack [h,a])+1) = a
  simp only [field,cursor,applyValue,outer,middle,inner]

private theorem conjRun (x : Nat) (p q : Program 1) :
    run (conjunction p q) x = if run p x = 1 ∧ run q x = 1 then 1 else 0 :=
  actualConjunctionEvaluation 1 p q (x ::ᵥ nil)

private theorem bothOfConj {x : Nat} {p q : Program 1}
    (yes : run (conjunction p q) x = 1) : run p x = 1 ∧ run q x = 1 := by
  rw [conjRun] at yes
  split at yes <;> simp_all

private theorem matching (raw : Nat) (yes : run ordinarySingletonGuard raw = 1) :
    ∃ h q ty : Nat, unpackNode raw = some (4,[h,pair q 0+1]) ∧
      unpackNode q = some (3,[ty]) ∧ run singletonTypeSelector raw = ty := by
  obtain ⟨head, triggered⟩ := bothOfConj (show
    run (conjunction (header 4 2) (applyUnary singletonTypeGuard (field 1))) raw = 1 from yes)
  obtain ⟨fs,fields,len⟩ := (exact_CoverHeaderUnpackNode 4 2 raw).mp head
  rcases fs with _ | ⟨h,_ | ⟨a,_ | ⟨x,rest⟩⟩⟩ <;> simp at len
  have arg := sourceSecond fields
  rw [applyValue,arg] at triggered
  obtain ⟨cell, gates⟩ := bothOfConj (show run (conjunction cellGood
    (conjunction (applyUnary (header 3 1) cellHead) (applyUnary GorbowPRInternalControl.zeroTest cellTail))) a = 1
      from triggered)
  obtain ⟨leaf, nil⟩ := bothOfConj gates
  rw [applyValue] at leaf nil
  let q := run cellHead a
  have zeroEval : run GorbowPRInternalControl.zeroTest (run cellTail a) =
      if run cellTail a = 0 then 1 else 0 := evalZeroTest _
  rw [zeroEval] at nil
  have tail : run cellTail a = 0 := by split at nil <;> simp_all
  have read : chosenCell a = some (q,0) := by
    change (if run cellGood a = 1 then some (q,run cellTail a) else none) = _
    rw [if_pos cell,tail]
  have repr := codeOfCell read
  obtain ⟨tf,child,len2⟩ := (exact_CoverHeaderUnpackNode 3 1 q).mp leaf
  rcases tf with _ | ⟨ty,_ | ⟨x,rest⟩⟩ <;> simp at len2
  refine ⟨h,q,ty,?_,child,?_⟩
  · rw [← repr]
    exact fields
  · rw [singletonTypeSelector,applyValue,applyValue,arg]
    exact sourceFirst child

theorem exact_CoverOrdinarySingletonKBase : ExactCoverOrdinarySingletonKBase := by
  intro s B fit calibrated ctx raw
  change evaluate (ordinarySingletonKBase s B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw
  rw [ordinarySingletonKBase,evalBranch]
  change (if run ordinarySingletonGuard raw = 0 then evaluate B (ctx ::ᵥ raw ::ᵥ nil)
    else evaluate (ordinarySingletonKBranch s B) (ctx ::ᵥ raw ::ᵥ nil)) = _
  by_cases yes : run ordinarySingletonGuard raw = 1
  · obtain ⟨h,q,ty,read,head,selector⟩ := matching raw yes
    rw [yes,if_neg (by decide),ordinarySingletonKBranch,evalBranch,evalNormalize]
    change (if (if evaluate (onRaw (singletonArgumentTypeAt s)) (ctx ::ᵥ raw ::ᵥ nil) = 1
      then 1 else 0) = 0 then 0 else evaluate B (ctx ::ᵥ raw ::ᵥ nil)) = _
    rw [calibrated]
    by_cases zero : intrinsicWindow s ctx raw = 0
    · rw [zero]
      split <;> rfl
    · have found := fit ty (exact_CoverOrdinarySingletonSourceType s ctx raw h q ty read head zero)
      have finite : run (singletonArgumentTypeAt s) raw = 1 := by
        rw [singletonArgumentTypeAt,applyValue,selector]
        exact memberOne s ty found
      have tested : evaluate (onRaw (singletonArgumentTypeAt s)) (ctx ::ᵥ raw ::ᵥ nil) = 1 := finite
      have nonzero : (if evaluate (onRaw (singletonArgumentTypeAt s)) (ctx ::ᵥ raw ::ᵥ nil) = 1
          then (1 : Nat) else 0) ≠ 0 := by
        rw [if_pos tested]
        exact Nat.one_ne_zero
      exact if_neg nonzero
  · have zero : run ordinarySingletonGuard raw = 0 := by
      unfold ordinarySingletonGuard at *
      rw [conjRun] at yes ⊢
      split <;> simp_all
    rw [if_pos zero]
    exact calibrated ctx raw

theorem exact_CoverOrdinarySingletonKWindowCalibrated : ExactCoverOrdinarySingletonKWindowCalibrated := by
  intro s B T fit base scalar
  exact exact_CoverLambdaLexicalWindow s (ordinarySingletonKBase s B) T fit
    (exact_CoverOrdinarySingletonKBase s B fit base) scalar

#print axioms exact_CoverOrdinarySingletonKBase
#print axioms exact_CoverOrdinarySingletonKWindowCalibrated

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowNumericProof
