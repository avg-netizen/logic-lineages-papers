module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeEncodedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeExecutionProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof
open OriginalRawSyntaxTransportSemanticProof (semanticCost costEquation costFuelBound)
open OriginalStructuralNodeSizeSemanticProof OriginalStructuralNodeSizeEncodedProof

 def stateIterate : Nat → State → State
  | 0, state => state
  | count + 1, state => OriginalStructuralNodeSizeSemanticProof.stateStep (stateIterate count state)

 theorem stateIterateAdd (first second : Nat) (state : State) :
    stateIterate (first + second) state = stateIterate second (stateIterate first state) := by
  induction second with
  | zero => rfl
  | succ second ih =>
    change OriginalStructuralNodeSizeSemanticProof.stateStep (stateIterate (first + second) state) =
      OriginalStructuralNodeSizeSemanticProof.stateStep (stateIterate second (stateIterate first state))
    exact congrArg (OriginalStructuralNodeSizeSemanticProof.stateStep) ih

 theorem encodedIteration (count : Nat) (state : State) :
    OriginalStructuralNodeSize.iterateValue count (encodeState state) = encodeState (stateIterate count state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change OriginalStructuralNodeSize.transitionValue (OriginalStructuralNodeSize.iterateValue count (encodeState state)) = _
    rw [ih, encodedTransition]
    rfl

 theorem visitOneStep (d k raw : Nat) (rest results : List Nat)
    (h1 : arityValue raw = 1) :
    OriginalStructuralNodeSizeSemanticProof.stateStep ⟨1, visitValue d k raw :: rest, results⟩ =
      ⟨1, visitValue d (if tagValue raw = 1 then k + 1 else k) (firstValue raw) ::
        finishValue raw :: rest, results⟩ := by
  simp [OriginalStructuralNodeSizeSemanticProof.stateStep, visitValue, h1]

 theorem visitTwoStep (d k raw : Nat) (rest results : List Nat)
    (h2 : arityValue raw = 2) :
    OriginalStructuralNodeSizeSemanticProof.stateStep ⟨1, visitValue d k raw :: rest, results⟩ =
      ⟨1, visitValue d k (firstValue raw) :: visitValue d k (secondValue raw) ::
        finishValue raw :: rest, results⟩ := by
  have h1 : arityValue raw ≠ 1 := by omega
  simp [OriginalStructuralNodeSizeSemanticProof.stateStep, visitValue, h1, h2]

 theorem finishOneStep (raw first : Nat) (rest results : List Nat)
    (h1 : arityValue raw = 1) :
    OriginalStructuralNodeSizeSemanticProof.stateStep ⟨1, finishValue raw :: rest, first :: results⟩ =
      ⟨1, rest, OriginalStructuralNodeSize.rebuildValue raw first 0 :: results⟩ := by
  simp [OriginalStructuralNodeSizeSemanticProof.stateStep, finishValue, h1]

 theorem finishTwoStep (raw first second : Nat) (rest results : List Nat)
    (h2 : arityValue raw = 2) :
    OriginalStructuralNodeSizeSemanticProof.stateStep ⟨1, finishValue raw :: rest, second :: first :: results⟩ =
      ⟨1, rest, OriginalStructuralNodeSize.rebuildValue raw first second :: results⟩ := by
  have h1 : arityValue raw ≠ 1 := by omega
  simp [OriginalStructuralNodeSizeSemanticProof.stateStep, finishValue, h1, h2]

/-- Exact execution preserves arbitrary work and result suffixes. This proves
successful traversal by structural arithmetic, rather than equating termination
with a correct singleton result. No well-typedness or source premise occurs. -/
 theorem visitExecution : ∀ (raw d k : Nat) (rest results : List Nat),
    stateIterate (semanticCost raw) ⟨1, visitValue d k raw :: rest, results⟩ =
      ⟨1, rest, semanticFold d k raw :: results⟩ := by
  intro raw
  induction raw using Nat.strong_induction_on with
  | h raw ih =>
    intro d k rest results
    by_cases h1 : arityValue raw = 1
    · have hb := unaryChildBound raw h1
      rw [costEquation, if_pos h1, semanticEquation, if_pos h1]
      rw [stateIterateAdd (1 + semanticCost (firstValue raw)) 1,
        stateIterateAdd 1 (semanticCost (firstValue raw))]
      change OriginalStructuralNodeSizeSemanticProof.stateStep (stateIterate (semanticCost (firstValue raw))
        (OriginalStructuralNodeSizeSemanticProof.stateStep ⟨1, visitValue d k raw :: rest, results⟩)) = _
      rw [visitOneStep d k raw rest results h1,
        ih (firstValue raw) (by omega) d (if tagValue raw = 1 then k + 1 else k)
          (finishValue raw :: rest) results,
        finishOneStep raw _ rest results h1]
    · by_cases h2 : arityValue raw = 2
      · have hb := binaryChildrenBound raw h2
        rw [costEquation, if_neg h1, if_pos h2, semanticEquation, if_neg h1, if_pos h2]
        rw [stateIterateAdd (1 + semanticCost (firstValue raw) + semanticCost (secondValue raw)) 1,
          stateIterateAdd (1 + semanticCost (firstValue raw)) (semanticCost (secondValue raw)),
          stateIterateAdd 1 (semanticCost (firstValue raw))]
        change OriginalStructuralNodeSizeSemanticProof.stateStep (stateIterate (semanticCost (secondValue raw))
          (stateIterate (semanticCost (firstValue raw))
            (OriginalStructuralNodeSizeSemanticProof.stateStep ⟨1, visitValue d k raw :: rest, results⟩))) = _
        rw [visitTwoStep d k raw rest results h2,
          ih (firstValue raw) (by omega) d k
            (visitValue d k (secondValue raw) :: finishValue raw :: rest) results,
          ih (secondValue raw) (by omega) d k (finishValue raw :: rest)
            (semanticFold d k (firstValue raw) :: results),
          finishTwoStep raw _ _ rest results h2]
      · rw [costEquation, if_neg h1, if_neg h2, semanticEquation, if_neg h1, if_neg h2]
        simp [stateIterate, OriginalStructuralNodeSizeSemanticProof.stateStep, visitValue, h1, h2]

 theorem finishedIterate (count : Nat) (results : List Nat) :
    stateIterate count ⟨1, [], results⟩ = ⟨1, [], results⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => simp [stateIterate, ih, OriginalStructuralNodeSizeSemanticProof.stateStep]

 theorem runAtSufficientCost (d k raw count : Nat) (h : semanticCost raw ≤ count) :
    OriginalStructuralNodeSize.iterateValue count (initialValue d k raw) =
      encodeState ⟨1, [], [semanticFold d k raw]⟩ := by
  change OriginalStructuralNodeSize.iterateValue count (encodeState ⟨1, [visitValue d k raw], []⟩) = _
  rw [encodedIteration]
  have hc : count = semanticCost raw + (count - semanticCost raw) := (Nat.add_sub_of_le h).symm
  rw [hc, stateIterateAdd, visitExecution, finishedIterate]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeExecutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeExecutionProof
