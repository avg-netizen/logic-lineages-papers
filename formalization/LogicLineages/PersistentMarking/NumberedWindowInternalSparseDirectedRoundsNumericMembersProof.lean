module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericRoundsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericMembersProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursion (listRec)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowInternalSparseDirectedRounds
open NumberedWindowInternalSparseDirectedRoundsTargets
open NumberedWindowInternalSparseDirectedRoundsNumericRoundsProof (allRounds)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)

private abbrev lengthStep : Program 2 :=
  .composition .succ (fun _ : Fin 1 => .projection 1)

private theorem lengthStepValue (h r : Nat) :
    evaluate lengthStep (h ::ᵥ r ::ᵥ nil) = Nat.succ r := rfl

private theorem lengthFold (values : List Nat) :
    values.foldr (fun h r => evaluate lengthStep (h ::ᵥ r ::ᵥ nil)) 0 =
      values.length := by
  induction values with
  | nil => rfl
  | cons h tail ih =>
    rw [List.foldr_cons, lengthStepValue, ih] <;> rfl

private theorem lengthValue (vertices : Nat) :
    evaluate poolLength (vertices ::ᵥ nil) = ((decodeNumbers vertices).getD []).length := by
  change evaluate (listRec (constantZero 0) lengthStep) (vertices ::ᵥ nil) = _
  rw [actualRawListRecursionEvaluation 0 (constantZero 0) lengthStep (nil : List.Vector Nat 0) vertices]
  exact lengthFold ((decodeNumbers vertices).getD [])

private theorem fuelValue (vertices ctx ty seed : Nat) :
    evaluate selectedFuel (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      ((decodeNumbers vertices).getD []).length :=
  lengthValue vertices

theorem allMembers : ExactAllInputDirectedMembers := by
  intro E vertices ctx ty seed
  rw [vectorFour]
  change evaluate (rounds E) (List.Vector.ofFn
    (roundsTape (evaluate selectedFuel (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil))
      vertices ctx ty seed)) = _
  rw [fuelValue]
  exact allRounds E ((decodeNumbers vertices).getD []).length vertices ctx ty seed

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericMembersProof
