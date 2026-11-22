module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowNumericProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultNumericProof
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
open NumberedWindowInternalCoverLexicalBoundWindowNumericProof (exact_CoverLexicalNamedWindowCalibrated)
open NumberedWindowInternalCoverNamedResultTargets

private theorem fieldValue {raw tag ty i : Nat} (read : unpackNode raw = some (tag,[ty,i])) :
    run (field 0) raw = ty := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt tag (pack [ty,i]))).2
  have inner : run cellHead (pack [ty,i]) = ty := (headTailOfCell (cellAt ty (pack [i]))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair tag (pack [ty,i]) + 1) = ty
  simp only [field,cursor,applyValue,outer,inner]

private theorem annotation {raw ty i : Nat} (b : Bool)
    (read : unpackNode raw = some (b.toNat,[ty,i])) : intrinsicType raw = ty := by
  cases b
  · have parse : unpackNode raw = some (0,[ty,i]) := read
    simp only [intrinsicType,NumberedWindowAnnotationAlgorithm.annotations,
      NumberedWindowAnnotationAlgorithm.termNext,parse,Option.map_some,Option.getD_some,
      NumberedWindowAnnotationAlgorithm.termParts] <;> rfl
  · have parse : unpackNode raw = some (1,[ty,i]) := read
    simp only [intrinsicType,NumberedWindowAnnotationAlgorithm.annotations,
      NumberedWindowAnnotationAlgorithm.termNext,parse,Option.map_some,Option.getD_some,
      NumberedWindowAnnotationAlgorithm.termParts] <;> rfl

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

private theorem storedValue (ctx raw : Nat) :
    evaluate storedTypeResult (ctx ::ᵥ raw ::ᵥ nil) = run (field 0) raw + 1 := rfl

theorem exact_CoverNamedResultAt : ExactCoverNamedResultAt := by
  intro b s B calibrated ctx raw
  change evaluate (namedResultAt b B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw
  rw [namedResultAt,evalBranch,onRawValue]
  by_cases good : run (header b.toNat 2) raw = 1
  · obtain ⟨fields,parse,len⟩ := (exact_CoverHeaderUnpackNode b.toNat 2 raw).mp good
    rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    rw [good,if_neg (by decide),namedPositiveResult,evalBranch,calibrated ctx raw,storedValue,fieldValue parse]
    cases h : packedWindow s ctx (intrinsicType raw) raw
    · have zero : intrinsicWindow s ctx raw = 0 := by simp [intrinsicWindow,h]
      rw [zero,if_pos rfl] <;> rfl
    · have out : intrinsicWindow s ctx raw = ty + 1 := by
        rw [intrinsicWindow,if_pos h,annotation b parse]
      rw [out,if_neg (Nat.succ_ne_zero ty)]
  · have zero : run (header b.toNat 2) raw = 0 := by
      have bit : run (header b.toNat 2) raw = 0 ∨ run (header b.toNat 2) raw = 1 := by
        unfold run header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bit.resolve_right good
    rw [if_pos zero]
    exact calibrated ctx raw

theorem exact_CoverNamedResultWindowCalibrated : ExactCoverNamedResultWindowCalibrated := by
  intro s B T included base types
  have named := exact_CoverNamedResultAt false s (namedResultAt true B) (exact_CoverNamedResultAt true s B base)
  exact exact_CoverLexicalNamedWindowCalibrated s (namedResultBase B) T included named types

#print axioms exact_CoverNamedResultAt
#print axioms exact_CoverNamedResultWindowCalibrated

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultNumericProof
