module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (decodeNumbers numbersNumber)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseDirectedRounds

def exactEdgeBit (E : Program 4) (ctx ty w v : Nat) : Bool :=
  decide (evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1)

/-- The literal original rounds recursion on every supplied scratch list
code, original seed and fuel, without a valid-window premise. -/
def ExactAllInputDirectedRounds : Prop :=
  ∀ (E : Program 4) (fuel vertices ctx ty seed : Nat),
    evaluate (rounds E) (List.Vector.ofFn (roundsTape fuel vertices ctx ty seed)) =
      numbersNumber (NumberedWindowClassAlgorithm.rounds (exactEdgeBit E ctx ty)
        ((decodeNumbers vertices).getD []) seed fuel)

/-- The exact original members output at the physical length fuel
computed from the same supplied pool. No minimum is taken here. -/
def ExactAllInputDirectedMembers : Prop :=
  ∀ (E : Program 4) (vertices ctx ty seed : Nat),
    evaluate (members E) (List.Vector.ofFn (membersTape vertices ctx ty seed)) =
      numbersNumber (NumberedWindowClassAlgorithm.members (exactEdgeBit E ctx ty)
        ((decodeNumbers vertices).getD []) seed)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
