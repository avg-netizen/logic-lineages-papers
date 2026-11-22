module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalSlotNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorThree)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowFieldAlgorithm (unpackNode unpack pack)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType)
open NumberedWindowInternalSparsePathEnvelope (run field cursor)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell packOfUnpack)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverNamedLeafIntrinsicNumericProof (exact_CoverNamedLeafGrammarWindowCalibrated)
open NumberedWindowInternalCoverLexicalSlotTargets (slotCheck)
open NumberedWindowInternalCoverLexicalSlotNumericProof (exact_CoverPhysicalLexicalSlot)
open NumberedWindowInternalCoverLexicalBoundWindowTargets

private theorem actualFields {raw ty i : Nat} (read : unpackNode raw = some (1,[ty,i])) :
    run (field 0) raw = ty ∧ run (field 1) raw = i := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt 1 (pack [ty,i]))).2
  have first : run cellHead (pack [ty,i]) = ty := (headTailOfCell (cellAt ty (pack [i]))).1
  have middle : run cellTail (pack [ty,i]) = pack [i] := (headTailOfCell (cellAt ty (pack [i]))).2
  have last : run cellHead (pack [i]) = i := (headTailOfCell (cellAt i (pack []))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair 1 (pack [ty,i]) + 1) = ty ∧
    run (field 1) (NumberedWindowPairAlgorithm.pair 1 (pack [ty,i]) + 1) = i
  simp only [field,cursor,applyValue,outer,first,middle,last] <;> simp

/-- Actual source lexical obligation, not a premise that the new guard
is numerically correct on undecodable packed contexts. -/
private theorem actualIndex (s : Settings) (ctx raw ty i : Nat) (read : unpackNode raw = some (1,[ty,i]))
    (positive : intrinsicWindow s ctx raw ≠ 0) : ∃ g, unpack ctx = some g ∧ g[i]? = some ty := by
  have yes : packedWindow s ctx (intrinsicType raw) raw = true := by
    cases h : packedWindow s ctx (intrinsicType raw) raw
    · exact False.elim (positive (by simp [intrinsicWindow,h]))
    · rfl
  cases hctx : unpack ctx with
  | none => simp [packedWindow,hctx] at yes
  | some g =>
    have yes' : admitted s g (intrinsicType raw) raw = true := by
      simpa only [packedWindow,hctx,Option.any_some] using yes
    have typed := (Bool.and_eq_true_iff.mp yes').1
    have held := (Bool.and_eq_true_iff.mp typed).2
    have held' : NumberedWindowLexicalAlgorithm.holds (fun j => g[j]?) (NumberedWindowLexicalAlgorithm.slot i ty) = true := by
      have req : (NumberedWindowLexicalAlgorithm.requirements raw).1 = NumberedWindowLexicalAlgorithm.slot i ty := by
        simp only [NumberedWindowLexicalAlgorithm.requirements,NumberedWindowLexicalAlgorithm.termNext,read,Option.map_some,Option.getD_some,
          NumberedWindowLexicalAlgorithm.termParts] <;> rfl
      simpa only [req] using held
    have hit : (g[i]? == some ty) = true := by
      simpa [NumberedWindowLexicalAlgorithm.holds,NumberedWindowLexicalAlgorithm.slot] using held'
    refine ⟨g,?_,beq_iff_eq.mp hit⟩
    first | exact hctx | rfl

private theorem guarded (ctx raw i ty : Nat) (fs : run (field 0) raw = ty ∧ run (field 1) raw = i)
    (haveSlot : evaluate slotCheck (i ::ᵥ ctx ::ᵥ ty ::ᵥ nil) = 1) :
    evaluate lexicalGuard (ctx ::ᵥ raw ::ᵥ nil) = 1 := by
  change evaluate slotCheck (List.Vector.ofFn (fun j =>
    evaluate ((![onRaw (field 1),.projection 0,onRaw (field 0)] : Fin 3 → Program 2) j) (ctx ::ᵥ raw ::ᵥ nil))) = 1
  rw [vectorThree]
  change evaluate slotCheck (run (field 1) raw ::ᵥ ctx ::ᵥ run (field 0) raw ::ᵥ nil) = 1
  rw [fs.2,fs.1]
  exact haveSlot

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

theorem exact_CoverLexicalBoundBase : ExactCoverLexicalBoundBase := by
  intro s B calibrated ctx raw
  change evaluate (lexicalBoundBase B) (ctx ::ᵥ raw ::ᵥ nil) = intrinsicWindow s ctx raw
  rw [lexicalBoundBase,evalBranch,onRawValue]
  by_cases actual : run (header 1 2) raw = 1
  · obtain ⟨fields,read,len⟩ := (exact_CoverHeaderUnpackNode 1 2 raw).mp actual
    rcases fields with _ | ⟨ty,_ | ⟨i,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
    rw [actual,if_neg (by decide),evalBranch,evalNormalize]
    by_cases absent : intrinsicWindow s ctx raw = 0
    · have zero : evaluate (constantZero 2) (ctx ::ᵥ raw ::ᵥ nil) = 0 := rfl
      rw [calibrated ctx raw,absent,zero]
      split <;> rfl
    · obtain ⟨g,unpacked,hit⟩ := actualIndex s ctx raw ty i read absent
      have slot : evaluate slotCheck (i ::ᵥ ctx ::ᵥ ty ::ᵥ nil) = 1 := by
        rw [packOfUnpack ctx unpacked]
        exact exact_CoverPhysicalLexicalSlot g i ty hit
      rw [guarded ctx raw i ty (actualFields read) slot]
      exact calibrated ctx raw
  · have zero : run (header 1 2) raw = 0 := by
      have bit : run (header 1 2) raw = 0 ∨ run (header 1 2) raw = 1 := by
        unfold run header NumberedWindowInternalSparsePathEnvelope.nodeGood
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bit.resolve_right actual
    rw [if_pos zero]
    exact calibrated ctx raw

theorem exact_CoverLexicalNamedWindowCalibrated : ExactCoverLexicalNamedWindowCalibrated := by
  intro s B T included base types
  exact exact_CoverNamedLeafGrammarWindowCalibrated s (lexicalBoundBase B) T included
    (exact_CoverLexicalBoundBase s B base) types

#print axioms exact_CoverLexicalBoundBase
#print axioms exact_CoverLexicalNamedWindowCalibrated

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLexicalBoundWindowNumericProof
