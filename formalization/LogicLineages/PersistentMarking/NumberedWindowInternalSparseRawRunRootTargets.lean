module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTick (rootCall chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (ownRun)

/-- Literal original root witness: tag zero, exactly one payload field. -/
def rootWitnessTerm {α : Type} (payload : OTerm α) : OTerm α :=
  rawCons z (rawCons payload z)

/-- The actual tick at a literal root witness returns the actual root
call's supplied output as the flag, with no frame. The old flag, both
raw endpoints, the payload and the output are arbitrary open terms; the
output is not assumed Boolean. -/
def ExactOpenRootTick : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type)
    (flag q payload r c : OTerm α),
    let w := rootWitnessTerm payload
    Nonempty (Derivation body [] ((programGraph (rootCall p) c ![q,w,r]).imp
      (programGraph (chosenTick p other) (stateTerm c z)
        ![stateTerm flag (frameValueTerm q w r)])))

/-- On a literal root tape the actual own run reads one exactly when the
supplied root program itself outputs one at the unwrapped payload. The
root program is an arbitrary `Program 3`: this is the machine's root
branch, not a statement that any particular program is the original
root relation. -/
def ExactOpenRootOwnRun : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (q payload r : OTerm α),
    let accepts := programGraph p (suc z) ![q,payload,r]
    let run := programGraph (ownRun p other) (suc z) ![q,rootWitnessTerm payload,r]
    Nonempty (Derivation body [] ((accepts.imp run) ⊓ (run.imp accepts)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
