module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdge
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowFieldAlgorithm (unpack)

abbrev exchangeTape {T : Type} (w v : T) : Fin 2 → T := ![w,v]
abbrev windowTape {T : Type} (ctx ty q : T) : Fin 3 → T := ![ctx,ty,q]

/-- Original lexical context: one successful ordered unpack or rejection.
In particular a failed packed code is not replaced by an empty context. -/
def packedEdge (s : Settings) (ctx ty w v : Nat) : Bool :=
  (unpack ctx).any (fun g => edge s g ty w v)

/-- On the directed [ctx,ty,w,v] tape, use the original term exchange bit. -/
def exchangeCall (X : Program 2) : Program 4 :=
  .composition X ![.projection 2,.projection 3]

/-- The same packed context, requested type, and W guard are retained for both ends. -/
def sourceWindow (W : Program 3) : Program 4 :=
  .composition W ![.projection 0,.projection 1,.projection 2]

def targetWindow (W : Program 3) : Program 4 :=
  .composition W ![.projection 0,.projection 1,.projection 3]

/-- Supply exactly this physical E to both the directed scan and filter.
It is not a newly compiled extensional replacement for those three calls. -/
def edge4 (X : Program 2) (W : Program 3) : Program 4 :=
  conjunction (exchangeCall X) (conjunction (sourceWindow W) (targetWindow W))

def edgeGraph (X : Program 2) (W : Program 3) {α : Type} (ctx ty w v : OTerm α) : Formula α :=
  programGraph (edge4 X W) (suc z) (edgeTape ctx ty w v)

def edgeCalls (X : Program 2) (W : Program 3) {α : Type} (ctx ty w v : OTerm α) : Formula α :=
  programGraph X (suc z) (exchangeTape w v) ⊓
    (programGraph W (suc z) (windowTape ctx ty w) ⊓
      programGraph W (suc z) (windowTape ctx ty v))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdge
