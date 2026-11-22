module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalPrecedingIntrinsicProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactPredecessorEvaluation)
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
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell packOfUnpack)
open NumberedWindowInternalStrictAuxWindowNumericProof (exact_StrictAuxWindowCalibration)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverTypeLeafIntrinsicNumericProof (exact_CoverTypeLeafIntrinsicWindowCalibrated)
open NumberedWindowInternalCoverHeadDispatchCalibrationProof (exact_CoverHeadFittedWindowCalibrated)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne)
open NumberedWindowInternalCoverLambdaLexicalSourceProof (exact_CoverLambdaPackedLexicalProvenance)
open NumberedWindowInternalCoverLambdaLexicalPrecedingIntrinsicProof (exact_CoverLambdaPrecedingIntrinsic)
open NumberedWindowInternalCoverNumberedTypeWindowNumericProof (exact_CoverNumberedTypeWindowCalibrated)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets

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

private theorem fields {raw dom q : Nat} (parse : unpackNode raw = some (2,[dom,q])) :
    run (field 0) raw = dom ∧ run (field 1) raw = q := by
  rw [codeOfNode parse]
  have outer := (headTailOfCell (cellAt 2 (pack [dom,q]))).2
  have fs : run cellHead (pack [dom,q]) = dom ∧ run cellTail (pack [dom,q]) = pack [q] :=
    headTailOfCell (cellAt dom (pack [q]))
  have final : run cellHead (pack [q]) = q := (headTailOfCell (cellAt q (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 2 (pack [dom,q]) + 1) = dom ∧
    run (field 1) (NumberedWindowPairAlgorithm.pair 2 (pack [dom,q]) + 1) = q
  simp only [field,cursor,applyValue,outer,fs.1,fs.2,final] <;> simp

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

private theorem oneValue {n : Nat} (P : Program 1) (Q : Program n) (xs : List.Vector Nat n) :
    evaluate (callOne P Q) xs = evaluate P (evaluate Q xs ::ᵥ nil) := by
  change evaluate P (List.Vector.ofFn (fun _ : Fin 1 => evaluate Q xs)) = _
  rw [vectorOne]

private theorem binaryValue {n : Nat} (P : Program 2) (a b : Program n) (xs : List.Vector Nat n) :
    evaluate (binary P a b) xs = evaluate P (evaluate a xs ::ᵥ evaluate b xs ::ᵥ nil) := by
  unfold binary
  rw [NumberedWindowInternalFreshProbeDispatchProgramControlProof.compositeTwo]

theorem exact_CoverLambdaLexicalBase : ExactCoverLambdaLexicalBase := by
  intro s B T fit base scalar ctx raw
  let xs := ctx ::ᵥ raw ::ᵥ nil
  change evaluate (lambdaLexicalBase s B T) xs = intrinsicWindow s ctx raw
  rw [lambdaLexicalBase,evalBranch]
  change (if run (header 2 2) raw = 0 then evaluate B xs else evaluate (lambdaPositive s B T) xs) = _
  by_cases yes : run (header 2 2) raw = 1
  · obtain ⟨fs,parse,len⟩ := (exact_CoverHeaderUnpackNode 2 2 raw).mp yes
    rcases fs with _ | ⟨dom,_ | ⟨q,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    rw [yes,if_neg (by decide),lambdaPositive,evalBranch]
    have calibration : evaluate B xs = intrinsicWindow s ctx raw := base ctx raw
    rw [calibration]
    by_cases zero : intrinsicWindow s ctx raw = 0
    · rw [if_pos zero,zero] <;> rfl
    · obtain ⟨g,unpackCtx,mem,child,parentOut⟩ := exact_CoverLambdaPackedLexicalProvenance s ctx raw dom q parse zero
      obtain ⟨first,second⟩ := fields parse
      have push : evaluate lambdaLexicalPush xs = pack (dom::g) := by
        rw [lambdaLexicalPush,binaryValue]
        change evaluate fieldCons (run (field 0) raw ::ᵥ ctx ::ᵥ nil) = _
        rw [first,packOfUnpack ctx unpackCtx,consValue]
        rfl
      have childOut : evaluate (lambdaOldBody s B T) xs = intrinsicType q + 1 := by
        rw [lambdaOldBody,binaryValue,push]
        change evaluate (precedingIntrinsic s B T) (pack (dom::g) ::ᵥ run (field 1) raw ::ᵥ nil) = _
        rw [second,exact_CoverLambdaPrecedingIntrinsic s B T fit base scalar (pack (dom::g)) q,child]
      have guard : evaluate (onRaw (leafTypeTest s)) xs = 1 := by
        change run (grammarTypeAt s) (run (field 0) raw) = 1
        rw [first,memberOne s dom (fit dom mem)]
      rw [if_neg zero,lambdaCheckedDomain,evalBranch,evalNormalize,guard]
      simp only [if_true,Nat.one_ne_zero,if_false]
      rw [lambdaCheckedBody,evalBranch,childOut,if_neg (Nat.succ_ne_zero _),lambdaLexicalResult,oneValue,lambdaArrowCode,
        binaryValue,oneValue,childOut,exactPredecessorEvaluation]
      change (evaluate fieldCons (run (field 0) raw ::ᵥ intrinsicType q ::ᵥ nil)) + 1 = _
      rw [first,consValue,parentOut] <;> rfl
  · have zero : run (header 2 2) raw = 0 := by
      have bits : run (header 2 2) raw = 0 ∨ run (header 2 2) raw = 1 := by
        unfold run header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bits.resolve_right yes
    rw [if_pos zero]
    exact base ctx raw

theorem exact_CoverLambdaLexicalWindow : ExactCoverLambdaLexicalWindow := by
  intro s B T fit base scalar
  exact exact_CoverNumberedTypeWindowCalibrated s (lambdaLexicalBase s B T) T fit
    (exact_CoverLambdaLexicalBase s B T fit base scalar) scalar

#print axioms exact_CoverLambdaLexicalBase
#print axioms exact_CoverLambdaLexicalWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowNumericProof
