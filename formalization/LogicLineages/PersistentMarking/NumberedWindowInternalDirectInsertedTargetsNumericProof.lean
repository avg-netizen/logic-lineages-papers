module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowDirectAlgorithm (readEntry entries)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt rawTriple)
open NumberedWindowInternalDirectWitnessNumericProof (exact_DirectSelectedEntry)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (vectorOne vectorTwo compositeOne literalEvaluation zeroEvaluation predEvaluation branchEvaluation bothEvaluation)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalDirectInsertedTargetsMapTargets

private theorem atHeadValue (p : Program 1) (raw prior : Nat) :
    evaluate (atHead p) (raw ::ᵥ prior ::ᵥ nil) = run p raw := by
  unfold atHead
  rw [evaluate,vectorOne]
  rfl

private theorem selected (a t d c : Nat) (h : readEntry a = some (t,d,c)) :
    run (guardAt 4) a = 1 ∧ run (field 0) a = t := by
  rw [← exact_DirectSelectedEntry a] at h
  unfold rawTriple at h
  split at h
  · rename_i yes
    exact ⟨yes,congrArg Prod.fst (Option.some.inj h)⟩
  · contradiction

private theorem absent (a : Nat) (h : readEntry a = none) :
    run (guardAt 4) a ≠ 1 := by
  rw [← exact_DirectSelectedEntry a] at h
  intro yes
  simp [rawTriple,yes] at h

private theorem joinedValue (raw prior : Nat) :
    evaluate joined (raw ::ᵥ prior ::ᵥ nil) = 1 + Nat.pair (run (field 0) raw) prior.pred := by
  unfold joined
  rw [evaluate,vectorTwo]
  change evaluate ID1Completion.InternalListCodec.consCode
    (evaluate (atHead (field 0)) (raw ::ᵥ prior ::ᵥ nil) ::ᵥ
      evaluate tailPayload (raw ::ᵥ prior ::ᵥ nil) ::ᵥ nil) = _
  rw [atHeadValue]
  have tail : evaluate tailPayload (raw ::ᵥ prior ::ᵥ nil) = prior.pred := by
    unfold tailPayload
    rw [evaluate,vectorOne]
    exact predEvaluation prior
  rw [tail,consEvaluation]

private theorem stepValue (row : Nat) (prior : Option (List Nat)) :
    evaluate targetStep (row ::ᵥ encodeResult prior ::ᵥ nil) =
      encodeResult (do let e ← readEntry row; let xs ← prior; pure (e.1 :: xs)) := by
  unfold targetStep
  rw [branchEvaluation,bothEvaluation,literalEvaluation,atHeadValue]
  cases got : readEntry row with
  | none =>
    have no := absent row got
    simp [no,encodeResult,zeroEvaluation]
  | some e =>
    obtain ⟨target,dominator,witness⟩ := e
    obtain ⟨yes,q⟩ := selected row target dominator witness got
    rw [yes]
    simp only [and_self,if_pos rfl,if_neg (Nat.succ_ne_zero 0),branchEvaluation,zeroEvaluation]
    cases prior with
    | none => rfl
    | some xs =>
      change (if numbersNumber xs + 1 = 0 then 0 else
        evaluate (.composition .succ (Fin.cons joined Fin.elim0))
          (row ::ᵥ (numbersNumber xs+1) ::ᵥ nil)) = numbersNumber (target :: xs) + 1
      rw [if_neg (Nat.succ_ne_zero _),compositeOne]
      change evaluate joined (row ::ᵥ (numbersNumber xs+1) ::ᵥ nil) + 1 = _
      rw [joinedValue,q]
      rfl

private theorem mappedCons (row : Nat) (rs : List Nat) :
    mapped (row :: rs) = (do let e ← readEntry row; let xs ← mapped rs; pure (e.1 :: xs)) := by
  change (Option.map (List.map Prod.fst) (do
    let e ← readEntry row
    let es ← entries rs
    pure (e :: es))) = (do
      let e ← readEntry row
      let xs ← Option.map (List.map Prod.fst) (entries rs)
      pure (e.1 :: xs))
  cases readEntry row <;> cases entries rs <;> rfl

theorem exact_OriginalScratchTargetsNumeric : ExactScratchTargets := by
  intro rows
  unfold scratchTargets
  rw [actualRawListRecursionEvaluation,numbersRoundTrip]
  change rows.foldr (fun a b => evaluate targetStep (a ::ᵥ b ::ᵥ nil)) (evaluate targetBase nil) =
    encodeResult (mapped rows)
  have base : evaluate targetBase nil = 1 := literalEvaluation 0 1 _
  rw [base]
  induction rows with
  | nil => rfl
  | cons row rs ih =>
    rw [List.foldr_cons,ih,stepValue,mappedCons]

theorem exact_OriginalRawInsertedTargetsNumeric : ExactRawInsertedTargets := by
  intro raw
  unfold insertedTargets
  rw [branchEvaluation,exact_ActualEncodedOutput,zeroEvaluation]
  cases u : unpack raw with
  | none => rfl
  | some rows =>
    change (if numbersNumber rows + 1 = 0 then 0 else
      evaluate (.composition scratchTargets (Fin.cons parserPayload Fin.elim0)) (raw ::ᵥ nil)) =
        encodeResult (mapped rows)
    rw [if_neg (Nat.succ_ne_zero _),compositeOne]
    have val : evaluate parserPayload (raw ::ᵥ nil) = numbersNumber rows := by
      unfold parserPayload
      rw [compositeOne,predEvaluation,exact_ActualEncodedOutput,u]
      rfl
    rw [val,exact_OriginalScratchTargetsNumeric]

#print axioms exact_OriginalScratchTargetsNumeric
#print axioms exact_OriginalRawInsertedTargetsNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsNumericProof
