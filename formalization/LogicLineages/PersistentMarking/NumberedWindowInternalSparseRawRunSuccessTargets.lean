module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (ownState ownRun)

/-- A successor (nonzero) flag read by the actual own run is equivalent
to the actual own state being the terminal scratch with that same flag
and frame zero. Tape, flag predecessor and both callback programs are
arbitrary; in particular the flag is not assumed to be one. This is a
statement about the machine scratch only: it gives no raw, least or
typed meaning to the accepted tape. -/
def ExactOpenOwnRunSuccessTerminal : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (q w r k : OTerm α),
    let run := programGraph (ownRun p other) (suc k) ![q,w,r]
    let terminal := programGraph (ownState p other) (stateTerm (suc k) z) ![q,w,r]
    Nonempty (Derivation body [] ((run.imp terminal) ⊓ (terminal.imp run)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessTargets
