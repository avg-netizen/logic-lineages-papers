module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (iterateState ownRun)

/-- True first-tick shift of the same physical recursor, in both
directions, for the same literal programs and the same output term. The
only premise is the supplied genuine tick graph: no scratch shape,
typing or callback assumption. -/
def ExactOpenRawFirstTickShift : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (start next fuel out : OTerm α),
    let tick := programGraph (chosenTick p other) next ![start]
    let late := programGraph (iterateState p other) out ![suc fuel,start]
    let early := programGraph (iterateState p other) out ![fuel,next]
    Nonempty (Derivation body [] (tick.imp ((late.imp early) ⊓ (early.imp late))))

/-- Extra fuel at a reached terminal scratch. The original start is an
arbitrary term kept distinct from the reached output; the larger fuel
is related by the original object order, not by a numeral bound. -/
def ExactOpenRawTerminalExtraFuel : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type) (flag start fuel more : OTerm α),
    let terminal := stateTerm flag z
    Nonempty (Derivation body [] ((ltF fuel more).imp
      ((programGraph (iterateState p other) terminal ![fuel,start]).imp
        (programGraph (iterateState p other) terminal ![more,start]))))

/-- A terminal run from the next scratch on its own fuel lifts to the
previous scratch at any strictly larger fuel. -/
def ExactOpenRawRunLift : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type)
    (flag start next fuel more : OTerm α),
    let terminal := stateTerm flag z
    Nonempty (Derivation body [] ((programGraph (chosenTick p other) next ![start]).imp
      ((ltF fuel more).imp
        ((programGraph (iterateState p other) terminal ![fuel,next]).imp
          (programGraph (iterateState p other) terminal ![more,start])))))

/-- The literal tag5 witness code strictly exceeds its raw child in the
original object order, for an arbitrary open child. -/
def ExactOpenFunctionWitnessStrict : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (child : OTerm α),
    Nonempty (Derivation body [] (ltF child (functionWitnessTerm child)))

/-- An own-code successful child run (fuel and stored witness both the
raw child) lifts through the literal tag5 function frame to the own-code
run of the wrapped parent, with the same successor flag. Both callback
programs, both annotations, the shared raw argument and all three raw
fields are arbitrary. This is machine acceptance only: it does not
assert raw or least semantics, typing, or RawMatching for either tape. -/
def ExactOpenLiftedOwnRun : Prop :=
  ∀ (body : Positive (Fin 1)) (p other : Program 3) (α : Type)
    (dom cod arg source child dest k : OTerm α),
    let src := auxiliaryTerm dom cod source arg
    let wr := functionWitnessTerm child
    let dst := auxiliaryTerm dom cod dest arg
    Nonempty (Derivation body []
      ((programGraph (ownRun p other) (suc k) ![source,child,dest]).imp
        (programGraph (ownRun p other) (suc k) ![src,wr,dst])))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets
