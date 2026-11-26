module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (iterateState)

/-- The actual raw recursor preserves exactly its original zero-frame
scratch at arbitrary open fuel and flag, under any object body.
Both physical branch programs are arbitrary and unconsulted. -/
def ExactOpenRawTerminalLoop : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (flag fuel : OTerm α),
    let st := stateTerm flag z
    Nonempty (Derivation body [] (programGraph (iterateState p other) st ![fuel,st]))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalTargets
