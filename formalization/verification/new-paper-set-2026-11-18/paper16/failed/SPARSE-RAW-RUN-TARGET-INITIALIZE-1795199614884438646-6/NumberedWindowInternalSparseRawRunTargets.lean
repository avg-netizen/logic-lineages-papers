module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowRawContextAlgorithm (RawRoot State iterate run)
open NumberedWindowInternalSparseRawTick (encodeState)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawRun (initialize iterateState ownRun)

def ExactOriginalRunInitialization : Prop :=
  ∀ q w r, evaluate initialize (q ::ᵥ w ::ᵥ r ::ᵥ nil) =
    encodeState (false,some (q,w,r))

/-- All original states and arbitrary genuine numeric fuel. No meaning
is asserted for arbitrary bytes outside the private scratch codec. -/
def ExactOriginalRawIteration : Prop :=
  ∀ (root : RawRoot) (p other : Program 3), ActualRoot root p → ActualFallback other →
    ∀ (fuel : Nat) (s : State),
      evaluate (iterateState p other) (fuel ::ᵥ encodeState s ::ᵥ nil) =
        encodeState (iterate root fuel s)

/-- The original run on every raw input, with its own literal w as
fuel and witness. This is not the outer typed windowStep. -/
def ExactOriginalOwnRawRun : Prop :=
  ∀ (root : RawRoot) (p other : Program 3), ActualRoot root p → ActualFallback other →
    ∀ (q w r : Nat), evaluate (ownRun p other) (q ::ᵥ w ::ᵥ r ::ᵥ nil) =
      (run root w q w r).toNat

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTargets
