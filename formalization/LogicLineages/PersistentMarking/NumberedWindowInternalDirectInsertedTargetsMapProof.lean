module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMap
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedWindowInternalDirectInsertedTargetsMapTargets
open NumberedWindowInternalDirectWitnessEnvelopeTargets (rawTriple guardAt)
open NumberedWindowInternalDirectWitnessEnvelope (exactRawTriple)
open NumberedWindowInternalSparsePathEnvelope (field run)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne chooseBranch literal predOne zeroAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (bothEvaluation branchEvaluation literalEvaluation predEvaluation zeroEvaluation compositeOne compositeTwo)
open NumberedWindowDirectAlgorithm (readEntry entries)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)

private theorem readExact (n : Nat) : rawTriple 4 n = readEntry n := by
  rw [exactRawTriple]
  unfold readEntry
  cases h : unpackNode n with
  | none => rfl
  | some p =>
    obtain ⟨tag,xs⟩ := p
    rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,rest⟩⟩⟩⟩ <;>
      rcases tag with _ | _ | _ | _ | _ | tag <;> rfl

private theorem headValue (p : Program 1) (row prev : Nat) :
    evaluate (atHead p) (row ::ᵥ prev ::ᵥ nil) = run p row := by
  unfold atHead
  rw [compositeOne] <;> rfl

private theorem joinedValue (row : Nat) (ts : List Nat) :
    evaluate joined (row ::ᵥ encodeResult (some ts) ::ᵥ nil) =
      numbersNumber (run (field 0) row :: ts) := by
  unfold joined tailPayload
  rw [compositeTwo,headValue,compositeOne]
  change evaluate consCode (run (field 0) row ::ᵥ
    evaluate predOne ((numbersNumber ts + 1) ::ᵥ nil) ::ᵥ nil) = _
  rw [predEvaluation, Nat.pred_succ, consEvaluation] <;> rfl

private theorem mappedCons (row : Nat) (rows : List Nat) :
    mapped (row :: rows) = (do
      let e ← rawTriple 4 row
      let ts ← mapped rows
      pure (e.1 :: ts)) := by
  unfold mapped
  rw [entries,readExact row]
  cases readEntry row <;> cases entries rows <;> rfl

private theorem stepValue (row : Nat) (rows : List Nat) :
    evaluate targetStep (row ::ᵥ encodeResult (mapped rows) ::ᵥ nil) =
      encodeResult (mapped (row :: rows)) := by
  unfold targetStep
  rw [branchEvaluation,bothEvaluation,headValue,literalEvaluation,mappedCons]
  by_cases hg : run (guardAt 4) row = 1
  · simp only [rawTriple,hg,true_and,if_true,Nat.one_ne_zero,if_false]
    rw [branchEvaluation,zeroEvaluation]
    cases hm : mapped rows with
    | none => rfl
    | some ts =>
      have nz : ¬ numbersNumber ts + 1 = 0 := Nat.succ_ne_zero _
      change (if numbersNumber ts + 1 = 0 then 0 else
        evaluate (.composition .succ (Fin.cons joined Fin.elim0))
          (row ::ᵥ encodeResult (some ts) ::ᵥ nil)) = _
      rw [if_neg nz,compositeOne,joinedValue] <;> rfl
  · simp only [rawTriple,hg,false_and,if_false,if_true,zeroEvaluation] <;> rfl

private theorem foldValue (rows : List Nat) :
    rows.foldr (fun row prev => evaluate targetStep (row ::ᵥ prev ::ᵥ nil))
      (evaluate targetBase (nil : List.Vector Nat 0)) = encodeResult (mapped rows) := by
  induction rows with
  | nil => exact literalEvaluation 0 1 _
  | cons row rows ih => rw [List.foldr_cons,ih,stepValue]

theorem exactScratchTargets : ExactScratchTargets := by
  intro rows
  have h := actualRawListRecursionEvaluation 0 targetBase targetStep nil (numbersNumber rows)
  rw [numbersRoundTrip] at h
  exact h.trans (foldValue rows)

theorem exactRawInsertedTargets : ExactRawInsertedTargets := by
  intro raw
  let xs : List.Vector Nat 1 := raw ::ᵥ nil
  have parsed : evaluate parser xs = encodeResult (unpack raw) := exact_ActualEncodedOutput raw
  change evaluate insertedTargets xs = _
  unfold insertedTargets
  rw [branchEvaluation,parsed,zeroEvaluation]
  cases h : unpack raw with
  | none => rfl
  | some rows =>
    have nz : ¬ numbersNumber rows + 1 = 0 := Nat.succ_ne_zero _
    change (if numbersNumber rows + 1 = 0 then 0 else
      evaluate (.composition scratchTargets (Fin.cons parserPayload Fin.elim0)) xs) =
        encodeResult (mapped rows)
    rw [if_neg nz,compositeOne,parserPayload,compositeOne,parsed,h]
    change evaluate scratchTargets
      (evaluate predOne ((numbersNumber rows + 1) ::ᵥ nil) ::ᵥ nil) = _
    rw [predEvaluation,Nat.pred_succ]
    exact exactScratchTargets rows

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMap
