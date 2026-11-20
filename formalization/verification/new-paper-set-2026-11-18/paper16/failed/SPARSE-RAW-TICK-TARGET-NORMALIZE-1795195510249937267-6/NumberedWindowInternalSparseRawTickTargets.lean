module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowRawContextAlgorithm (RawRoot State tick)
open NumberedWindowInternalSparsePathEnvelopeTargets (z rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (encodeFrame)
open NumberedWindowInternalSparseRawFunctionFrameTargets
  (auxiliaryTerm functionWitnessTerm frameValueTerm)
open NumberedWindowInternalSparseRawTick

def ActualRoot (root : RawRoot) (p : Program 3) : Prop :=
  ∀ q w r, evaluate p (q ::ᵥ w ::ᵥ r ::ᵥ nil) = (root q w r).toNat

def ActualFallback (p : Program 3) : Prop :=
  ∀ q w r, evaluate p (q ::ᵥ w ::ᵥ r ::ᵥ nil) = encodeFrame (fallbackValue q w r)

/-- An actual executable choice, not an unproved caller oracle. -/
def ExactConcreteFallback : Prop := ∃ p : Program 3, ActualFallback p

/-- Full original branch comparison on every raw tape. Both original
root and contextual leaves are explicit numeric interfaces. -/
def ExactOriginalLiveTick : Prop :=
  ∀ (root : RawRoot) (p other : Program 3), ActualRoot root p → ActualFallback other →
    ∀ (flag : Bool) (q w r : Nat),
      evaluate (liveTick p other) (q ::ᵥ w ::ᵥ r ::ᵥ nil) =
        encodeState (tick root (flag,some (q,w,r)))

/-- Compare checking at the explicit encoding of every original state,
not an attempt to change the interpretation of arbitrary scratch bytes. -/
def ExactOriginalEncodedTick : Prop :=
  ∀ (root : RawRoot) (p other : Program 3), ActualRoot root p → ActualFallback other →
    ∀ s : State,
      evaluate (chosenTick p other) (encodeState s ::ᵥ nil) = encodeState (tick root s)

def stateTerm {α : Type} (flag frame : OTerm α) : OTerm α :=
  rawCons flag (rawCons frame z)

/-- Actual zero-frame scratch is unchanged in the original calculus.
The flag is an arbitrary ordinary term; neither callback is consulted. -/
def ExactOpenTerminalTick : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (flag : OTerm α),
    let st := stateTerm flag z
    Nonempty (Derivation body [] (programGraph (chosenTick p other) st ![st]))

/-- The actual unary physical tick opens its live scratch, dispatches
on literal original tag5, and returns the actual child scratch unchanged
in source/witness/destination order. No root/fallback semantics used. -/
def ExactOpenLiftedTick : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type)
    (flag dom cod arg source child dest : OTerm α),
    let src := auxiliaryTerm dom cod source arg
    let wr := functionWitnessTerm child
    let dst := auxiliaryTerm dom cod dest arg
    let initial := stateTerm flag (frameValueTerm src wr dst)
    let final := stateTerm z (frameValueTerm source child dest)
    Nonempty (Derivation body [] (programGraph (chosenTick p other) final ![initial]))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
