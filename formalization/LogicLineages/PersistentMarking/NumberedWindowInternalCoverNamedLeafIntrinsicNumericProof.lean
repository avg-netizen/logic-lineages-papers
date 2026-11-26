module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafIntrinsicNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowNumericProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowAdmissionAlgorithm (rawBits bits termNext termParts)
open NumberedWindowFieldAlgorithm (unpackNode unpack pack)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalStrictAuxWindowNumericProof (exact_StrictAuxWindowCalibration)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalCoverTypeLeafIntrinsicNumericProof (exact_CoverTypeLeafIntrinsicWindowCalibrated)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets

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

private theorem fieldValue {raw tag ty i : Nat} (read : unpackNode raw = some (tag,[ty,i])) :
    run (field 0) raw = ty := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt tag (pack [ty,i]))).2
  have inner : run cellHead (pack [ty,i]) = ty := (headTailOfCell (cellAt ty (pack [i]))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair tag (pack [ty,i]) + 1) = ty
  simp only [field,cursor,applyValue,outer,inner]

private theorem leafMember (b : Bool) (s : Settings) (ctx raw ty i : Nat)
    (read : unpackNode raw = some (b.toNat,[ty,i]))
    (positive : intrinsicWindow s ctx raw ≠ 0) : ty ∈ s.window.1 := by
  have yes : packedWindow s ctx (intrinsicType raw) raw = true := by
    cases h : packedWindow s ctx (intrinsicType raw) raw
    · exact False.elim (positive (by simp [intrinsicWindow,h]))
    · rfl
  cases hctx : unpack ctx with
  | none => simp [packedWindow,hctx] at yes
  | some g =>
    have yes' : admitted s g (intrinsicType raw) raw = true := by
      simpa only [packedWindow,hctx,Option.any_some] using yes
    rw [admitted,Bool.and_eq_true] at yes'
    have goodBits := yes'.2
    change ((NumberedWindowSyntaxAlgorithm.syntaxBits raw).1 && (rawBits s.window raw).1) = true at goodBits
    have admittedLeaf : (rawBits s.window raw).1 = true := (Bool.and_eq_true_iff.mp goodBits).2
    apply List.contains_iff_mem.mp
    have fieldZero : ([ty,i] : List Nat).getD 0 0 = ty := rfl
    cases b
    · have h : unpackNode raw = some (0,[ty,i]) := read
      simpa only [rawBits,termNext,h,Option.any_some,termParts,fieldZero] using admittedLeaf
    · have h : unpackNode raw = some (1,[ty,i]) := read
      simpa only [rawBits,termNext,h,Option.any_some,termParts,fieldZero] using admittedLeaf

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

private theorem probeValue (s : Settings) (raw : Nat) : run (leafTypeTest s) raw =
    run (grammarTypeAt s) (run (field 0) raw) := rfl

theorem exact_CoverNamedLeafGrammarAt : ExactCoverNamedLeafGrammarAt := by
  intro b s B included calibrated ctx raw
  change evaluate (namedGrammarAt b s B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw
  rw [namedGrammarAt,evalBranch,onRawValue]
  by_cases actual : run (header b.toNat 2) raw = 1
  · obtain ⟨fields,parse,len⟩ := (exact_CoverHeaderUnpackNode b.toNat 2 raw).mp actual
    rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    rw [actual,if_neg (by decide),grammarGuard,evalBranch,evalNormalize,onRawValue,probeValue s raw,fieldValue parse]
    by_cases absent : intrinsicWindow s ctx raw = 0
    · have zero : evaluate (constantZero 2) (ctx ::ᵥ raw ::ᵥ nil) = 0 := rfl
      rw [calibrated ctx raw,absent,zero]
      split <;> rfl
    · have k := included ty (leafMember b s ctx raw ty i parse absent)
      rw [memberOne s ty k]
      exact calibrated ctx raw
  · have zero : run (header b.toNat 2) raw = 0 := by
      have bit : run (header b.toNat 2) raw = 0 ∨ run (header b.toNat 2) raw = 1 := by
        unfold run header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bit.resolve_right actual
    rw [if_pos zero]
    exact calibrated ctx raw

theorem exact_CoverNamedLeafGrammarWindowCalibrated : ExactCoverNamedLeafGrammarWindowCalibrated := by
  intro s B T included base types
  have bound := exact_CoverNamedLeafGrammarAt true s B included base
  have named := exact_CoverNamedLeafGrammarAt false s (namedGrammarAt true s B) included bound
  exact exact_CoverTypeLeafIntrinsicWindowCalibrated s (namedGrammarBase s B) T included named types

#print axioms exact_CoverNamedLeafGrammarAt
#print axioms exact_CoverNamedLeafGrammarWindowCalibrated

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicNumericProof
