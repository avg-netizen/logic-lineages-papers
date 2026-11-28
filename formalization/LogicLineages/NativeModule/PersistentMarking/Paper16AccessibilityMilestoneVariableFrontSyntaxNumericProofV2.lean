module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

/-! Numeric proofs of the frozen `VariableSyntaxBit` and `VariableFrontSyntaxCalibrated`
(`Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2`; Fable B2, 27 November 2026).
The pattern is that of `NumberedWindowInternalCoverNamedLeafMeasureNumericProof`, which does the
same for the measure leaf. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxNumericProofV2

open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (syntaxBits termNext termParts table)
open NumberedWindowFieldAlgorithm (unpackNode pack)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood applyUnary)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2

private theorem typeFieldValue {raw tag h : Nat} {tail : List Nat}
    (read : unpackNode raw = some (tag, h :: tail)) : run (field 0) raw = h := by
  rw [codeOfNode read]
  have outer := (headTailOfCell (cellAt tag (pack (h :: tail)))).2
  have inner : run cellHead (pack (h :: tail)) = h := (headTailOfCell (cellAt h (pack tail))).1
  change run (field 0) (NumberedWindowPairAlgorithm.pair tag (pack (h :: tail)) + 1) = h
  simp only [field, cursor, applyValue, outer, inner]

private theorem headerBits (tag n : Nat) :
    run (header tag 2) n = 0 ∨ run (header tag 2) n = 1 := by
  simp only [run, header, nodeGood]
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem variableTermBit {raw ty i : Nat} (read : unpackNode raw = some (0, [ty, i])) :
    (syntaxBits raw).1 = typeBit ty := by
  change (unpackNode raw).any (fun p => termParts
    (fun q => ((table raw).getD q (false, false)).1)
    (fun a => ((table raw).getD a (false, false)).2) p.1 p.2) = typeBit ty
  rw [read]
  rfl

theorem exact_VariableSyntaxBit : VariableSyntaxBit := by
  intro TV typeFit raw leaf
  obtain ⟨fields, parse, len⟩ := (exact_CoverHeaderUnpackNode 0 2 raw).mp leaf
  rcases fields with _ | ⟨ty, _ | ⟨i, _ | ⟨extra, rest⟩⟩⟩ <;> simp at len
  have value : run (variableCheck TV) raw = run TV (run (field 0) raw) :=
    applyValue TV (field 0) raw
  rw [value, typeFieldValue parse, typeFit ty, variableTermBit parse]

theorem exact_VariableFrontSyntaxCalibrated : VariableFrontSyntaxCalibrated := by
  intro TV V typeFit calibrated n
  change evaluate (branch (header 0 2) V (variableCheck TV)) (n ::ᵥ nil) = (syntaxBits n).1.toNat
  rw [evalBranch]
  rcases headerBits 0 n with zero | one
  · change evaluate (header 0 2) (n ::ᵥ nil) = 0 at zero
    rw [if_pos zero]
    exact calibrated n
  · have leaf : run isVariableNode n = 1 := one
    change evaluate (header 0 2) (n ::ᵥ nil) = 1 at one
    rw [one, if_neg (by decide)]
    exact exact_VariableSyntaxBit TV typeFit n leaf

#print axioms exact_VariableSyntaxBit
#print axioms exact_VariableFrontSyntaxCalibrated

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxNumericProofV2
