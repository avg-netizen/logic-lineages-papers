module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (Settings vertices)
open NumberedWindowInternalSparseFieldParserTargets (encodeResult)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualEncodedOutput)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverScratchNumericProjectionProof (scratchVerticesValue)
open NumberedWindowInternalSparseDirectedRounds (members)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparseDirectedRoundsNumericChecks (exact_AllInputDirectedMembers)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparsePackedLeast

theorem contextValue (ctx ty seed : Nat) :
    evaluate contextOption (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = encodeResult (unpack ctx) := by
  rw [contextOption, unaryValue]
  exact exact_ActualEncodedOutput ctx

private theorem poolValue (C : Program 3) (hC : ActualSelectedCoverOutput C)
    (s : Settings) (ctx ty seed : Nat) :
    evaluate (poolAtSeed C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = numbersNumber (vertices s seed) := by
  rw [poolAtSeed, unaryValue]
  exact scratchVerticesValue C hC s seed

theorem membersValue (C : Program 3) (X : Program 2) (W : Program 3)
    (hC : ActualSelectedCoverOutput C) (s : Settings) (ctx ty seed : Nat) :
    evaluate (membersAtSeed C X W s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      numbersNumber (NumberedWindowClassAlgorithm.members (exactEdgeBit (edge4 X W) ctx ty)
        (vertices s seed) seed) := by
  unfold membersAtSeed
  rw [evaluate, vectorFour]
  change evaluate (members (edge4 X W))
    (evaluate (poolAtSeed C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = _
  rw [poolValue C hC s ctx ty seed]
  have original := exact_AllInputDirectedMembers (edge4 X W) (numbersNumber (vertices s seed)) ctx ty seed
  rw [numbersRoundTrip, vectorFour] at original
  exact original

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
