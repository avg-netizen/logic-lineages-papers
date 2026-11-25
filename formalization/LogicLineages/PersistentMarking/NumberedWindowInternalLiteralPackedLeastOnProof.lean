module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (Settings vertices edge)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration encodeState packedLeast)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseCoverScratchNumericProjectionProof (scratchVerticesValue)
open NumberedWindowInternalSparseDirectedRounds (members)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparseDirectedRoundsNumericChecks (exact_AllInputDirectedMembers)
open NumberedWindowInternalSparseScalarEdge (edge4 packedEdge)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScalarEdgeNumericProof (calibration)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastNumericTapeProof (contextValue)
open NumberedWindowInternalSparsePackedLeastNumericMinimumProof (allInput)

def membersAtSeedOn (C : Program 3) (E : Program 4) (s : Settings) : Program 3 :=
  .composition (members E) ![poolAtSeed C s,.projection 0,.projection 1,.projection 2]

def minimumAtMembersOn (C : Program 3) (E : Program 4) (s : Settings) : Program 3 :=
  .composition scratchMinimum (fun _ : Fin 1 => membersAtSeedOn C E s)

/-- Exact original tape and class minimum, parameterized by the actually
selected four-slot edge checker. No other physical program changes. -/
def packedLeastOn (C : Program 3) (E : Program 4) (s : Settings) : Program 3 :=
  branch contextOption (constantZero 3) (minimumAtMembersOn C E s)

def leastOnGraph {α : Type} (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed selected : OTerm α) : Formula α :=
  programGraph (packedLeastOn C E s) (suc selected) ![ctx,ty,seed]

theorem packedLeastOnOriginal (C W : Program 3) (X : Program 2) (s : Settings) :
    packedLeastOn C (edge4 X W) s = packedLeastProgram C X W s := rfl

def ActualPackedEdgeOn (s : Settings) (E : Program 4) : Prop :=
  ∀ ctx ty g, unpack ctx = some g → exactEdgeBit E ctx ty = edge s g ty

theorem exact_OriginalPackedEdgeOn (s : Settings) (X : Program 2) (W : Program 3)
    (hX : ActualTermExchange s X) (hW : ActualPackedWindow s W) :
    ActualPackedEdgeOn s (edge4 X W) := by
  intro ctx ty g parsed
  funext w r
  unfold exactEdgeBit
  rw [calibration s X W hX hW ctx ty w r]
  have bit : packedEdge s ctx ty w r = edge s g ty w r := by
    rw [packedEdge,parsed] <;> rfl
  rw [bit]
  cases edge s g ty w r <;> rfl

private theorem poolValue (C : Program 3) (hC : ActualSelectedCoverOutput C) (s : Settings)
    (ctx ty seed : Nat) :
    evaluate (poolAtSeed C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = numbersNumber (vertices s seed) := by
  rw [poolAtSeed,unaryValue]
  exact scratchVerticesValue C hC s seed

private theorem membersValue (C : Program 3) (E : Program 4) (s : Settings)
    (hC : ActualSelectedCoverOutput C) (ctx ty seed : Nat) :
    evaluate (membersAtSeedOn C E s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      numbersNumber (NumberedWindowClassAlgorithm.members (exactEdgeBit E ctx ty) (vertices s seed) seed) := by
  unfold membersAtSeedOn
  rw [evaluate,vectorFour]
  change evaluate (members E)
    (evaluate (poolAtSeed C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = _
  rw [poolValue C hC s ctx ty seed]
  have original := exact_AllInputDirectedMembers E (numbersNumber (vertices s seed)) ctx ty seed
  rw [numbersRoundTrip,vectorFour] at original
  exact original

theorem exact_LiteralPackedLeastOn (C : Program 3) (E : Program 4) (s : Settings)
    (cover : ActualSelectedCoverOutput C) (fit : ActualPackedEdgeOn s E) :
    ActualLeastCalibration s (packedLeastOn C E s) := by
  intro ctx ty seed
  unfold packedLeast
  rw [packedLeastOn,evalBranch,contextValue]
  cases decoded : unpack ctx with
  | none => rfl
  | some g =>
    change (if numbersNumber g+1 = 0 then 0 else
      evaluate (minimumAtMembersOn C E s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil)) =
        encodeState (NumberedWindowScalarAlgorithm.least s g ty seed)
    rw [if_neg (Nat.succ_ne_zero (numbersNumber g)),minimumAtMembersOn,unaryValue,
      membersValue C E s cover ctx ty seed,allInput,numbersRoundTrip,fit ctx ty g decoded] <;> rfl

#print axioms packedLeastOnOriginal
#print axioms exact_OriginalPackedEdgeOn
#print axioms exact_LiteralPackedLeastOn
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
