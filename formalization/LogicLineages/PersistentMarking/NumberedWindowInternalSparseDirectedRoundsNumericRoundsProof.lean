module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericRoundsProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptance (constantZero)
open NumberedMultisetNumeric (numbersNumber decodeNumbers)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseDirectedFilter (pass passTape)
open NumberedWindowInternalSparseDirectedFilterNumericChecks (exact_AllInputDirectedFilter)
open NumberedWindowInternalSparseDirectedRounds
open NumberedWindowInternalSparseDirectedRoundsTargets
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (baseTape stepTape vectorFive)

private theorem zeroEdge (ctx ty w v : Nat) :
    decide (evaluate (constantZero 4) (List.Vector.ofFn (edgeTape ctx ty w v)) = 1) =
      false := rfl

private theorem baseValue (vertices ctx ty seed : Nat) :
    evaluate roundBase (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      numbersNumber (((decodeNumbers vertices).getD []).filter (fun v => seed == v)) := by
  rw [baseTape]
  have filtered := exact_AllInputDirectedFilter (constantZero 4)
    vertices (numbersNumber [seed]) ctx ty
  rw [numbersRoundTrip] at filtered
  have emptyAny (p : Nat → Bool) : ([] : List Nat).any p = false := rfl
  simpa only [NumberedWindowClassAlgorithm.advance, Option.getD_some, List.any_cons,
    emptyAny, zeroEdge, Bool.or_false] using filtered

/-- The literal and ordered original recursion at each arbitrary natural fuel. -/
theorem allRounds : ExactAllInputDirectedRounds := by
  intro E fuel vertices ctx ty seed
  rw [vectorFive]
  change evaluate (rounds E) (fuel ::ᵥ vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = _
  induction fuel with
  | zero =>
    change evaluate roundBase (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = _
    exact baseValue vertices ctx ty seed
  | succ index ih =>
    let pool := (decodeNumbers vertices).getD []
    let prev := NumberedWindowClassAlgorithm.rounds (exactEdgeBit E ctx ty) pool seed index
    change evaluate (roundStep E) (index ::ᵥ
      evaluate (rounds E) (index ::ᵥ vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) ::ᵥ
      vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      numbersNumber (NumberedWindowClassAlgorithm.advance (exactEdgeBit E ctx ty) pool prev)
    rw [stepTape,ih]
    change evaluate (pass E) (List.Vector.ofFn (passTape vertices (numbersNumber prev) ctx ty)) = _
    have filtered := exact_AllInputDirectedFilter E vertices (numbersNumber prev) ctx ty
    rw [numbersRoundTrip] at filtered
    exact filtered

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericRoundsProof
