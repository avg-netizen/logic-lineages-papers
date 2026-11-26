module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorThree)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverBoundsAlgorithm (cover)
open NumberedWindowScalarAlgorithm (Settings vertices)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation)
open NumberedWindowInternalSparseCoverScratch
open NumberedWindowInternalSparseCoverScratchTargets
open NumberedWindowInternalSparseCoverScratchNumericCodecProof (payload)

theorem coverOptionValue (C : Program 3) (hC : ActualSelectedCoverOutput C)
    (s : Settings) (n : Nat) :
    evaluate (coverOption C s) (n ::ᵥ nil) = Encodable.encode (cover s.window.2 s.types n) := by
  unfold coverOption
  rw [evaluate, vectorThree]
  change evaluate C (evaluate (literal 1 (Encodable.encode s.window.2)) (n ::ᵥ nil) ::ᵥ
    evaluate (literal 1 (Encodable.encode s.types)) (n ::ᵥ nil) ::ᵥ n ::ᵥ nil) = _
  simp only [literalEvaluation]
  exact hC s.window.2 s.types n

theorem scratchVerticesValue (C : Program 3) (hC : ActualSelectedCoverOutput C)
    (s : Settings) (n : Nat) :
    evaluate (scratchVertices C s) (n ::ᵥ nil) = numbersNumber (vertices s n) := by
  unfold scratchVertices
  rw [evaluate, vectorOne]
  change evaluate optionPayload (evaluate (coverOption C s) (n ::ᵥ nil) ::ᵥ nil) = _
  rw [coverOptionValue C hC s n]
  exact payload (cover s.window.2 s.types n)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
