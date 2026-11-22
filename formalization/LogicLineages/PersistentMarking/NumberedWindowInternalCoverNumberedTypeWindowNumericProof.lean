module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchCalibrationProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowNumericProof
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
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverTypeLeafIntrinsicNumericProof (exact_CoverTypeLeafIntrinsicWindowCalibrated)
open NumberedWindowInternalCoverHeadDispatchCalibrationProof (exact_CoverHeadFittedWindowCalibrated)
open NumberedWindowInternalCoverNumberedTypeWindowTargets

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

private theorem fieldValue {raw h ty : Nat} {tail : List Nat}
    (read : unpackNode raw = some (5,h::ty::tail)) : run (field 1) raw = ty := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 5 (pack (h::ty::tail)))).2
  have middle : run cellTail (pack (h::ty::tail)) = pack (ty::tail) :=
    (headTailOfCell (cellAt h (pack (ty::tail)))).2
  have last : run cellHead (pack (ty::tail)) = ty :=
    (headTailOfCell (cellAt ty (pack tail))).1
  change run (field 1) (NumberedWindowPairAlgorithm.pair 5 (pack (h::ty::tail)) + 1) = ty
  simp only [field,cursor,applyValue,outer,middle,last]

private theorem neededType (s : Settings) (ctx raw h ty : Nat) (tail : List Nat)
    (read : unpackNode raw = some (5,h::ty::tail))
    (positive : intrinsicWindow s ctx raw ≠ 0) : ty ∈ s.window.1 := by
  have yes : packedWindow s ctx (intrinsicType raw) raw = true := by
    cases r : packedWindow s ctx (intrinsicType raw) raw
    · exact False.elim (positive (by simp [intrinsicWindow,r]))
    · rfl
  cases hctx : unpack ctx with
  | none => simp [packedWindow,hctx] at yes
  | some g =>
    have yes' : admitted s g (intrinsicType raw) raw = true := by
      simpa only [packedWindow,hctx,Option.any_some] using yes
    rw [admitted,Bool.and_eq_true] at yes'
    have goodBits := yes'.2
    change ((NumberedWindowSyntaxAlgorithm.syntaxBits raw).1 && (rawBits s.window raw).1) = true at goodBits
    have yesRow : (rawBits s.window raw).1 = true := (Bool.and_eq_true_iff.mp goodBits).2
    have type1 : (h::ty::tail).getD 1 0 = ty := rfl
    simp only [rawBits,termNext,read,Option.any_some,termParts,type1,Bool.and_eq_true] at yesRow
    exact List.contains_iff_mem.mp yesRow.1.1.2

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

private theorem probeValue (s : Settings) (raw : Nat) : run (numberedGrammarType s) raw =
    run (grammarTypeAt s) (run (field 1) raw) := rfl

theorem exact_CoverNumberedTypeBase : ExactCoverNumberedTypeBase := by
  intro s B included calibrated ctx raw
  change evaluate (numberedTypeBase s B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw
  rw [numberedTypeBase,evalBranch,onRawValue]
  by_cases actual : run (header 5 5) raw = 1
  · obtain ⟨fields,parse,len⟩ := (exact_CoverHeaderUnpackNode 5 5 raw).mp actual
    rcases fields with _ | ⟨h,_ | ⟨ty,tail⟩⟩ <;> simp at len
    rw [actual,if_neg (by decide),numberedTypeGuard,evalBranch,evalNormalize,onRawValue,probeValue s raw,fieldValue parse]
    by_cases absent : intrinsicWindow s ctx raw = 0
    · have zero : evaluate (constantZero 2) (ctx ::ᵥ raw ::ᵥ nil) = 0 := rfl
      rw [calibrated ctx raw,absent,zero]
      split <;> rfl
    · have hk := included ty (neededType s ctx raw h ty tail parse absent)
      rw [memberOne s ty hk]
      exact calibrated ctx raw
  · have zero : run (header 5 5) raw = 0 := by
      have bit : run (header 5 5) raw = 0 ∨ run (header 5 5) raw = 1 := by
        unfold run header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bit.resolve_right actual
    rw [if_pos zero]
    exact calibrated ctx raw

theorem exact_CoverNumberedTypeWindowCalibrated : ExactCoverNumberedTypeWindowCalibrated := by
  intro s B T fit base guard
  exact exact_CoverHeadFittedWindowCalibrated s (numberedTypeBase s B) T fit
    (exact_CoverNumberedTypeBase s B fit base) guard

#print axioms exact_CoverNumberedTypeBase
#print axioms exact_CoverNumberedTypeWindowCalibrated

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowNumericProof
