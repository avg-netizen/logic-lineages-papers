module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

/-! Numeric proof of the frozen `VariableFrontWindowCalibrated`
(`Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2`; Fable B2, 27 November 2026). -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowNumericProofV2

open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowLexicalAlgorithm (requirements holds)
open NumberedWindowAdmissionAlgorithm (rawBits)
open NumberedWindowFieldAlgorithm (unpackNode unpack pack)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalAuxWindowMemoTargets
  (intrinsicWindow intrinsicType typeGuard IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalCoverHeaderFieldsNumericProof (exact_CoverHeaderUnpackNode)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope (run field cursor nodeGood applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2

private theorem onRawValue (P : Program 1) (ctx raw : Nat) :
    evaluate (onRaw P) (ctx ::ᵥ raw ::ᵥ nil) = run P raw := rfl

private theorem contextParsedValue (ctx raw : Nat) :
    evaluate contextParsed (ctx ::ᵥ raw ::ᵥ nil) = run parser ctx := rfl

private theorem successorRun (n : Nat) : run .succ n = n + 1 := rfl

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

/-- Admission of a free-variable node at its own annotation is the type guard of field 0. -/
private theorem leafAdmitted (s : Settings) (g : List Nat) {raw ty i : Nat}
    (read : unpackNode raw = some (0, [ty, i])) :
    admitted s g (intrinsicType raw) raw = typeGuard s ty := by
  have syn : (syntaxBits raw).1 = typeBit ty := by
    change (unpackNode raw).any (fun p => NumberedWindowSyntaxAlgorithm.termParts
      (fun q => ((NumberedWindowSyntaxAlgorithm.table raw).getD q (false, false)).1)
      (fun a => ((NumberedWindowSyntaxAlgorithm.table raw).getD a (false, false)).2) p.1 p.2) =
        typeBit ty
    rw [read]
    rfl
  have req : (requirements raw).1 = NumberedWindowLexicalAlgorithm.empty := by
    change ((unpackNode raw).map (fun p => NumberedWindowLexicalAlgorithm.termParts
      (NumberedWindowLexicalAlgorithm.table raw) p.1 p.2)).getD default =
        NumberedWindowLexicalAlgorithm.empty
    rw [read]
    rfl
  have rb : (rawBits s.window raw).1 = s.window.1.contains ty := by
    change (unpackNode raw).any (fun p => NumberedWindowAdmissionAlgorithm.termParts s.window
      (NumberedWindowAdmissionAlgorithm.table s.window raw) p.1 p.2) = s.window.1.contains ty
    rw [read]
    rfl
  have same : ((annotations raw).1 == (annotations raw).1) = true := beq_self_eq_true _
  have held : holds (fun i => g[i]?) NumberedWindowLexicalAlgorithm.empty = true := rfl
  change ((((syntaxBits raw).1 && ((annotations raw).1 == (annotations raw).1)) &&
      holds (fun i => g[i]?) (requirements raw).1) &&
    ((syntaxBits raw).1 && (rawBits s.window raw).1)) = (typeBit ty && s.window.1.contains ty)
  rw [syn, same, req, held, rb]
  generalize typeBit ty = a
  generalize s.window.1.contains ty = b
  cases a <;> cases b <;> rfl

/-- The intrinsic window at a free-variable node. -/
private theorem leafWindow (s : Settings) (ctx : Nat) {raw ty i : Nat}
    (read : unpackNode raw = some (0, [ty, i])) :
    intrinsicWindow s ctx raw = if (unpack ctx).isSome && typeGuard s ty then ty + 1 else 0 := by
  have ann : intrinsicType raw = ty := by
    change ((unpackNode raw).map (fun p => NumberedWindowAnnotationAlgorithm.termParts
      (NumberedWindowAnnotationAlgorithm.table raw) p.1 p.2)).getD 0 = ty
    rw [read]
    rfl
  have win : packedWindow s ctx (intrinsicType raw) raw =
      ((unpack ctx).isSome && typeGuard s ty) := by
    unfold packedWindow
    cases hctx : unpack ctx with
    | none => rfl
    | some g =>
      change admitted s g (intrinsicType raw) raw = typeGuard s ty
      exact leafAdmitted s g read
  change (if packedWindow s ctx (intrinsicType raw) raw = true then intrinsicType raw + 1 else 0) =
    if ((unpack ctx).isSome && typeGuard s ty) = true then ty + 1 else 0
  rw [win, ann]

/-- The explicit program at a free-variable node. -/
private theorem leafValue (s : Settings) (T : Program 1) (typeFit : TypeGuardCalibrated s T)
    (ctx : Nat) {raw ty i : Nat} (read : unpackNode raw = some (0, [ty, i])) :
    evaluate (variableWindowValue T) (ctx ::ᵥ raw ::ᵥ nil) =
      if (unpack ctx).isSome && typeGuard s ty then ty + 1 else 0 := by
  have guardValue : evaluate (variableGuard T) (ctx ::ᵥ raw ::ᵥ nil) = (typeGuard s ty).toNat := by
    rw [variableGuard, onRawValue, applyValue, typeFieldValue read]
    exact typeFit ty
  have resultValue : evaluate variableResult (ctx ::ᵥ raw ::ᵥ nil) = ty + 1 := by
    rw [variableResult, onRawValue, applyValue, typeFieldValue read, successorRun]
  have zero : evaluate (constantZero 2) (ctx ::ᵥ raw ::ᵥ nil) = 0 := rfl
  rw [variableWindowValue, evalBranch, contextParsedValue, evalBranch, guardValue, resultValue, zero]
  change (if evaluate parser (ctx ::ᵥ nil) = 0 then 0
    else if (typeGuard s ty).toNat = 0 then 0 else ty + 1) =
      if ((unpack ctx).isSome && typeGuard s ty) = true then ty + 1 else 0
  rw [exact_ActualEncodedOutput ctx]
  cases hctx : unpack ctx with
  | none => rfl
  | some g =>
    change (if numbersNumber g + 1 = 0 then 0
      else if (typeGuard s ty).toNat = 0 then 0 else ty + 1) =
        if typeGuard s ty = true then ty + 1 else 0
    rw [if_neg (Nat.succ_ne_zero (numbersNumber g))]
    generalize typeGuard s ty = b
    cases b <;> rfl

theorem exact_VariableFrontWindowCalibrated : VariableFrontWindowCalibrated := by
  intro s T base typeFit calibrated ctx raw
  change evaluate (branch (onRaw (header 0 2)) base (variableWindowValue T)) (ctx ::ᵥ raw ::ᵥ nil) =
    intrinsicWindow s ctx raw
  rw [evalBranch, onRawValue]
  rcases headerBits 0 raw with zero | one
  · rw [if_pos zero]
    exact calibrated ctx raw
  · obtain ⟨fields, parse, len⟩ := (exact_CoverHeaderUnpackNode 0 2 raw).mp one
    rcases fields with _ | ⟨ty, _ | ⟨i, _ | ⟨extra, rest⟩⟩⟩ <;> simp at len
    rw [one, if_neg (by decide), leafValue s T typeFit ctx parse, leafWindow s ctx parse]

#print axioms exact_VariableFrontWindowCalibrated

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowNumericProofV2
