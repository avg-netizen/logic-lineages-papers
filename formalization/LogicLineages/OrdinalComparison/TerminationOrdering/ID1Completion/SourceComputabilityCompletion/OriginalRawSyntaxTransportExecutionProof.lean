module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportExecutionProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof
open OriginalRawSyntaxTransportSemanticProof OriginalRawSyntaxTransportEncodedProof

 def stateIterate (mode : Mode) : Nat → State → State
  | 0, state => state
  | count + 1, state => stateStep mode (stateIterate mode count state)

 theorem stateIterateAdd (mode : Mode) (first second : Nat) (state : State) :
    stateIterate mode (first + second) state = stateIterate mode second (stateIterate mode first state) := by
  induction second with
  | zero => rfl
  | succ second ih =>
    change stateStep mode (stateIterate mode (first + second) state) =
      stateStep mode (stateIterate mode second (stateIterate mode first state))
    exact congrArg (stateStep mode) ih

 theorem encodedIteration (mode : Mode) (count : Nat) (state : State) :
    iterateValue mode count (encodeState state) = encodeState (stateIterate mode count state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change transitionValue mode (iterateValue mode count (encodeState state)) = _
    rw [ih, actualRawSyntaxEncodedTransition]
    rfl

 theorem visitOneStep (mode : Mode) (d k raw : Nat) (rest results : List Nat)
    (h1 : arityValue raw = 1) :
    stateStep mode ⟨1, visitValue d k raw :: rest, results⟩ =
      ⟨1, visitValue d (if tagValue raw = 1 then k + 1 else k) (firstValue raw) ::
        finishValue raw :: rest, results⟩ := by
  simp [stateStep, visitValue, h1]

 theorem visitTwoStep (mode : Mode) (d k raw : Nat) (rest results : List Nat)
    (h2 : arityValue raw = 2) :
    stateStep mode ⟨1, visitValue d k raw :: rest, results⟩ =
      ⟨1, visitValue d k (firstValue raw) :: visitValue d k (secondValue raw) ::
        finishValue raw :: rest, results⟩ := by
  have h1 : arityValue raw ≠ 1 := by omega
  simp [stateStep, visitValue, h1, h2]

 theorem finishOneStep (mode : Mode) (raw first : Nat) (rest results : List Nat)
    (h1 : arityValue raw = 1) :
    stateStep mode ⟨1, finishValue raw :: rest, first :: results⟩ =
      ⟨1, rest, rebuildValue mode raw first 0 :: results⟩ := by
  simp [stateStep, finishValue, h1]

 theorem finishTwoStep (mode : Mode) (raw first second : Nat) (rest results : List Nat)
    (h2 : arityValue raw = 2) :
    stateStep mode ⟨1, finishValue raw :: rest, second :: first :: results⟩ =
      ⟨1, rest, rebuildValue mode raw first second :: results⟩ := by
  have h1 : arityValue raw ≠ 1 := by omega
  simp [stateStep, finishValue, h1, h2]

/-- Exact execution preserves arbitrary work and result suffixes. This proves
successful traversal by structural arithmetic, rather than equating termination
with a correct singleton result. No well-typedness or source premise occurs. -/
 theorem visitExecution (mode : Mode) : ∀ (raw d k : Nat) (rest results : List Nat),
    stateIterate mode (semanticCost raw) ⟨1, visitValue d k raw :: rest, results⟩ =
      ⟨1, rest, semanticFold mode d k raw :: results⟩ := by
  intro raw
  induction raw using Nat.strong_induction_on with
  | h raw ih =>
    intro d k rest results
    by_cases h1 : arityValue raw = 1
    · have hb := unaryChildBound raw h1
      rw [costEquation, if_pos h1, semanticEquation, if_pos h1]
      rw [stateIterateAdd mode (1 + semanticCost (firstValue raw)) 1,
        stateIterateAdd mode 1 (semanticCost (firstValue raw))]
      change stateStep mode (stateIterate mode (semanticCost (firstValue raw))
        (stateStep mode ⟨1, visitValue d k raw :: rest, results⟩)) = _
      rw [visitOneStep mode d k raw rest results h1,
        ih (firstValue raw) (by omega) d (if tagValue raw = 1 then k + 1 else k)
          (finishValue raw :: rest) results,
        finishOneStep mode raw _ rest results h1]
    · by_cases h2 : arityValue raw = 2
      · have hb := binaryChildrenBound raw h2
        rw [costEquation, if_neg h1, if_pos h2, semanticEquation, if_neg h1, if_pos h2]
        rw [stateIterateAdd mode (1 + semanticCost (firstValue raw) + semanticCost (secondValue raw)) 1,
          stateIterateAdd mode (1 + semanticCost (firstValue raw)) (semanticCost (secondValue raw)),
          stateIterateAdd mode 1 (semanticCost (firstValue raw))]
        change stateStep mode (stateIterate mode (semanticCost (secondValue raw))
          (stateIterate mode (semanticCost (firstValue raw))
            (stateStep mode ⟨1, visitValue d k raw :: rest, results⟩))) = _
        rw [visitTwoStep mode d k raw rest results h2,
          ih (firstValue raw) (by omega) d k
            (visitValue d k (secondValue raw) :: finishValue raw :: rest) results,
          ih (secondValue raw) (by omega) d k (finishValue raw :: rest)
            (semanticFold mode d k (firstValue raw) :: results),
          finishTwoStep mode raw _ _ rest results h2]
      · rw [costEquation, if_neg h1, if_neg h2, semanticEquation, if_neg h1, if_neg h2]
        simp [stateIterate, stateStep, visitValue, h1, h2]

 theorem finishedIterate (mode : Mode) (count : Nat) (results : List Nat) :
    stateIterate mode count ⟨1, [], results⟩ = ⟨1, [], results⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simp [stateIterate, ih, stateStep]

 theorem runAtSufficientCost (mode : Mode) (d k raw count : Nat) (h : semanticCost raw ≤ count) :
    iterateValue mode count (initialValue d k raw) =
      encodeState ⟨1, [], [semanticFold mode d k raw]⟩ := by
  change iterateValue mode count (encodeState ⟨1, [visitValue d k raw], []⟩) = _
  rw [encodedIteration]
  have hc : count = semanticCost raw + (count - semanticCost raw) := (Nat.add_sub_of_le h).symm
  rw [hc, stateIterateAdd, visitExecution, finishedIterate]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportExecutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportExecutionProof
