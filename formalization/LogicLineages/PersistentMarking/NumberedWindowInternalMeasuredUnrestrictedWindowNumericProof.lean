module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowScalarAlgorithm (Settings vertices)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverScratchNumericProjectionProof (scratchVerticesValue)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparsePackedLeastNumericTapeProof (contextValue)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions

private theorem ownValue (C : Program 3) (s : Settings) (hC : ActualSelectedCoverOutput C)
    (ctx ty seed : Nat) : evaluate (ownSeed C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      ((vertices s seed).any (fun head => head == seed)).toNat := by
  let xs := ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil
  have v : evaluate (poolAtSeed C s) xs = numbersNumber (vertices s seed) := by
    rw [poolAtSeed,unaryValue]
    exact scratchVerticesValue C hC s seed
  change evaluate scratchMember (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![poolAtSeed C s,.projection 2] : Fin 2 → Program 3) i) xs)) = _
  rw [vectorTwo]
  change evaluate scratchMember (evaluate (poolAtSeed C s) xs ::ᵥ seed ::ᵥ nil) = _
  rw [v,NumberedWindowInternalSparseScratchMembershipNumericChecks.exact_AllInputScratchMembership,numbersRoundTrip]
  rfl

theorem exact_LiteralCoveredWindowCalibration : ExactCoveredWindowCalibration := by
  intro C s baseW hC covered original ctx ty seed
  let xs := ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil
  change evaluate (coveredWindow C s baseW) xs = _
  rw [coveredWindow,actualConjunctionEvaluation]
  have w : evaluate baseW xs = (packedWindow s ctx ty seed).toNat := original ctx ty seed
  rw [w]
  cases hit : packedWindow s ctx ty seed with
  | false => rfl
  | true =>
    obtain ⟨g,parse,accepted⟩ : ∃ g, unpack ctx = some g ∧ NumberedWindowScalarAlgorithm.admitted s g ty seed = true := by
      cases q : unpack ctx with
      | none => simp [packedWindow,q] at hit
      | some g => exact ⟨g,rfl,by simpa [packedWindow,q] using hit⟩
    have pc : evaluate contextPresent xs = 1 := by
      rw [contextPresent,evalBranch]
      change (if evaluate NumberedWindowInternalSparsePackedLeast.contextOption (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = 0 then _ else _) = _
      rw [contextValue,parse]
      rfl
    have q : evaluate (ownSeed C s) xs = 1 := by
      rw [ownValue C s hC ctx ty seed]
      simp [covered g ty seed accepted]
    rw [actualConjunctionEvaluation,pc,q]
    rfl
open NumberedWindowScalarAlgorithm (admitted)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

theorem exact_SyntaxWindowCalibration : ExactSyntaxWindowCalibration := by
  intro s baseW V original valid ctx ty seed
  rw [syntaxWindow,actualConjunctionEvaluation,original]
  cases h : packedWindow s ctx ty seed with
  | false => rfl
  | true =>
    have syntaxTrue : (syntaxBits seed).1 = true := by
      cases u : unpack ctx with
      | none => simp [packedWindow,u] at h
      | some xs =>
        have ok : admitted s xs ty seed = true := by simpa [packedWindow,u] using h
        exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ok).2).1
    rw [unaryValue]
    change (if 1 = 1 ∧ evaluate V (seed ::ᵥ nil) = 1 then 1 else 0) = _
    exact if_pos ⟨rfl,(valid seed).trans (by rw [syntaxTrue]; rfl)⟩

#print axioms exact_SyntaxWindowCalibration
#print axioms exact_LiteralCoveredWindowCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowNumericProof
