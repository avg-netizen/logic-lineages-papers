module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowNumericProof
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
open NumberedWindowInternalCoverHeadWindowTargets

private theorem listCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem memberOne (s : Settings) (ty : Nat) (member : ty ∈ s.window.2) : run (grammarHeadAt s) ty = 1 := by
  let T := s.window.2
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

private theorem fieldValue {raw tag h : Nat} {tail : List Nat}
    (read : unpackNode raw = some (tag,h::tail)) : run (field 0) raw = h := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt tag (pack (h::tail)))).2
  have inner : run cellHead (pack (h::tail)) = h := (headTailOfCell (cellAt h (pack tail))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair tag (pack (h::tail)) + 1) = h
  simp only [field,cursor,applyValue,outer,inner]

private theorem neededHead (b : Bool) (s : Settings) (ctx raw h : Nat) (tail : List Nat)
    (read : unpackNode raw = some (headTag b,h::tail))
    (positive : intrinsicWindow s ctx raw ≠ 0) : h ∈ s.window.2 := by
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
    have head0 : (h::tail).getD 0 0 = h := rfl
    apply List.contains_iff_mem.mp
    cases b
    · have parsed : unpackNode raw = some (4,h::tail) := read
      simp only [rawBits,termNext,parsed,Option.any_some,termParts,head0,Bool.and_eq_true] at yesRow
      exact yesRow.1
    · have parsed : unpackNode raw = some (5,h::tail) := read
      simp only [rawBits,termNext,parsed,Option.any_some,termParts,head0,Bool.and_eq_true] at yesRow
      exact yesRow.1.1.1

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

private theorem probeValue (s : Settings) (raw : Nat) : run (storedHeadInGrammar s) raw =
    run (grammarHeadAt s) (run (field 0) raw) := rfl

theorem exact_CoverHeadBaseAt : ExactCoverHeadBaseAt := by
  intro b s B calibrated ctx raw
  change evaluate (headBaseAt b s B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw
  rw [headBaseAt,evalBranch,onRawValue]
  by_cases actual : run (header (headTag b) (headArity b)) raw = 1
  · obtain ⟨fields,parse,len⟩ := (exact_CoverHeaderUnpackNode (headTag b) (headArity b) raw).mp actual
    cases fields with
    | nil => cases b <;> simp [headArity] at len
    | cons h tail =>
      rw [actual,if_neg (by decide),headPositive,evalBranch,evalNormalize,onRawValue,probeValue s raw,fieldValue parse]
      by_cases absent : intrinsicWindow s ctx raw = 0
      · have zero : evaluate (constantZero 2) (ctx ::ᵥ raw ::ᵥ nil) = 0 := rfl
        rw [calibrated ctx raw,absent,zero]
        split <;> rfl
      · have hk := neededHead b s ctx raw h tail parse absent
        rw [memberOne s h hk]
        exact calibrated ctx raw
  · have zero : run (header (headTag b) (headArity b)) raw = 0 := by
      have bit : run (header (headTag b) (headArity b)) raw = 0 ∨ run (header (headTag b) (headArity b)) raw = 1 := by
        unfold run header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bit.resolve_right actual
    rw [if_pos zero]
    exact calibrated ctx raw

theorem exact_CoverGrammarHeadBase : ExactCoverGrammarHeadBase := by
  intro s B calibrated
  exact exact_CoverHeadBaseAt false s (headBaseAt true s B) (exact_CoverHeadBaseAt true s B calibrated)

#print axioms exact_CoverHeadBaseAt
#print axioms exact_CoverGrammarHeadBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowNumericProof
