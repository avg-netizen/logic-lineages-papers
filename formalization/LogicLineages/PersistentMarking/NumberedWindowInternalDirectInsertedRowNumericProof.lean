module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open ID1Completion.InternalEqualityTestEvaluationProof
  (vectorOne vectorTwo vectorThree exactPredecessorEvaluation)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowDirectAlgorithm (readEntry)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseScratchMembershipNumericProof (allInput)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt rawTriple)
open NumberedWindowInternalDirectWitnessNumericProof (exact_DirectSelectedEntry)
open NumberedWindowInternalDirectInsertedRowTargets

private theorem parserValue (a b : Nat) :
    evaluate parseRemoved (a ::ᵥ b ::ᵥ nil) = encodeResult (unpack a) := by
  unfold parseRemoved liftLeft
  rw [evaluate,vectorOne]
  exact exact_ActualEncodedOutput a

theorem exact_InsertedPoolReadyNumeric (a b : Nat) :
    evaluate poolReady (a ::ᵥ b ::ᵥ nil) = (unpack a).isSome.toNat := by
  unfold poolReady
  rw [evalBranch,parserValue,literalEvaluation]
  cases h : unpack a with
  | none => rfl
  | some xs =>
    change (if numbersNumber xs + 1 = 0 then 0 else 1) = _
    rw [if_neg (Nat.succ_ne_zero _)]
    rfl

theorem exact_InsertedPoolCodeNumeric (a b : Nat) (xs : List Nat) (found : unpack a = some xs) :
    evaluate poolCode (a ::ᵥ b ::ᵥ nil) = numbersNumber xs := by
  unfold poolCode
  rw [evaluate,vectorOne]
  change evaluate ID1Completion.InternalEqualityTest.predecessor (evaluate parseRemoved (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
  rw [parserValue,found,exactPredecessorEvaluation]
  simp [encodeResult]

theorem exact_InsertedRowGuardNumeric (a b : Nat) :
    evaluate rowGuard (a ::ᵥ b ::ᵥ nil) = run (guardAt 4) b := by
  unfold rowGuard liftRight
  rw [evaluate,vectorOne]
  rfl

theorem exact_InsertedRowFieldNumeric (i a b : Nat) :
    evaluate (rowField i) (a ::ᵥ b ::ᵥ nil) = run (field i) b := by
  unfold rowField liftRight
  rw [evaluate,vectorOne]
  rfl

private theorem acceptedRow (a t d c : Nat) (h : readEntry a = some (t,d,c)) :
    run (guardAt 4) a = 1 ∧ run (field 0) a = t ∧ run (field 1) a = d ∧ run (field 2) a = c := by
  rw [← exact_DirectSelectedEntry a] at h
  unfold rawTriple at h
  split at h
  · rename_i yes
    have e := Option.some.inj h
    exact ⟨yes,congrArg Prod.fst e,congrArg (fun p => p.2.1) e,congrArg (fun p => p.2.2) e⟩
  · contradiction

private theorem rejectedRow (a : Nat) (h : readEntry a = none) :
    run (guardAt 4) a ≠ 1 := by
  rw [← exact_DirectSelectedEntry a] at h
  intro yes
  simp [rawTriple,yes] at h

private theorem memberValue (a b : Nat) (pool : List Nat) (f : unpack a = some pool) :
    evaluate memberAt (a ::ᵥ b ::ᵥ nil) =
       (pool.any (fun x => x == run (field 1) b)).toNat := by
  unfold memberAt
  rw [evaluate,vectorTwo]
  change evaluate NumberedWindowInternalSparseScratchMembership.scratchMember
    (evaluate poolCode (a ::ᵥ b ::ᵥ nil) ::ᵥ evaluate (rowField 1) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
  rw [exact_InsertedPoolCodeNumeric a b pool f,exact_InsertedRowFieldNumeric,allInput,numbersRoundTrip]
  rfl

private theorem positiveValue (r : Program 3) (a b : Nat) :
    evaluate (positiveAt r) (a ::ᵥ b ::ᵥ nil) = evaluate r
      (run (field 1) b ::ᵥ run (field 2) b ::ᵥ run (field 0) b ::ᵥ nil) := by
  unfold positiveAt
  rw [evaluate,vectorThree]
  change evaluate r (evaluate (rowField 1) (a ::ᵥ b ::ᵥ nil) ::ᵥ
    evaluate (rowField 2) (a ::ᵥ b ::ᵥ nil) ::ᵥ evaluate (rowField 0) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
  rw [exact_InsertedRowFieldNumeric,exact_InsertedRowFieldNumeric,exact_InsertedRowFieldNumeric]

theorem exact_OriginalInsertedRowNumeric : ExactNumericInsertedRow := by
  intro r rem row
  unfold insertedRow expected
  rw [conjunctionEvaluation,conjunctionEvaluation,conjunctionEvaluation,
    exact_InsertedRowGuardNumeric,exact_InsertedPoolReadyNumeric]
  cases pool : unpack rem with
  | none => simp
  | some xs =>
    cases entry : readEntry row with
    | none => simp [rejectedRow row entry]
    | some e =>
      obtain ⟨t,d,c⟩ := e
      obtain ⟨guard,f₀,f₁,f₂⟩ := acceptedRow row t d c entry
      rw [guard,memberValue rem row xs pool,positiveValue,f₀,f₁,f₂]
      cases h : xs.any (fun a => a == d) <;>
        by_cases checked : evaluate r (d ::ᵥ c ::ᵥ t ::ᵥ nil) = 1 <;>
        simp [h,checked,Bool.toNat]

#print axioms exact_InsertedPoolReadyNumeric
#print axioms exact_InsertedPoolCodeNumeric
#print axioms exact_InsertedRowGuardNumeric
#print axioms exact_InsertedRowFieldNumeric
#print axioms exact_OriginalInsertedRowNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedRowNumericProof
