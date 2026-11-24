module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionRunPeelProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionFrameInversionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm functionWitnessTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof (emit)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (emitGraph)
open NumberedWindowInternalSparseRawRun (ownRun iterateState)
open NumberedWindowInternalSparseRawRunLiftOwnProof (ownLoop initialTerm)
open NumberedWindowInternalSparseRawRunShiftProof (shiftEarly)
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (D initialTick)
open NumberedWindowInternalLiteralAuxFirstTickCasesProof (TickAt)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralFunctionRunPeelProof (functionRemaining childTape)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem functionTick (p other : Program 3) (q w r frame : OTerm α)
    (tag : D B Γ (bit tagFiveTest ![q,w,r]))
    (call : D B Γ (programGraph chosenFrame frame ![q,w,r])) :
    D B Γ (TickAt p other z frame q w r) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let F := auxiliaryFallback other
  let bad := emitState (constantZero 3) F
  let root := emitState (rootCall p) (constantZero 3)
  let fn := emitState (constantZero 3) chosenFrame
  have picked := successorBranchIntro tagFiveTest (branch rootTest bad root) fn
    (stateTerm z frame) z xs tag (emitGraph _ _ z frame xs (constantZeroValue xs) call)
  exact initialTick p F q w r _ picked

abbrev ChildTerminal (p other : Program 3) (fn child dest : OTerm α) : Formula α :=
  programGraph (iterateState p (auxiliaryFallback other)) (stateTerm (suc z) z)
    ![functionRemaining child,initialTerm (childTape fn child dest)]

/-- The successful function branch steps to the exact decoded child
triple; its new fuel is the exact predecessor of the original witness,
with no assumption that the target term is already typed. -/
theorem exact_OpenAuxiliaryRemainingChild (p other : Program 3) (q w r : OTerm α)
    (dom cod fn arg child dom' cod' dest arg' : OTerm α)
    (tag : D B Γ (bit tagFiveTest ![q,w,r]))
    (fields : Parts B Γ q w r dom cod fn arg child dom' cod' dest arg')
    (success : D B Γ (bit (ownRun p (auxiliaryFallback other)) ![q,w,r])) :
    D B Γ (ChildTerminal p other fn child dest) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let ys : Fin 3 → OTerm α := childTape fn child dest
  let F := auxiliaryFallback other
  let out : OTerm α := stateTerm (suc z) z
  let childFrame := frameValueTerm fn child dest
  have frame : D B Γ (programGraph chosenFrame childFrame xs) :=
    successorBranchIntro frameGood (constantZero 3) emitFrame childFrame z xs fields.ready.guard
      (emit xs fn child dest fields.ready)
  have tick := functionTick p other q w r childFrame tag frame
  have before := ownLoop p F out xs (ownRunTerminal p F z xs success)
  have witness : D B Γ (eqn w (suc (functionRemaining child))) := by
    simpa only [functionWitnessTerm,functionRemaining,rawCons] using fields.witness
  have late : D B Γ (programGraph (iterateState p F) out ![suc (functionRemaining child),initialTerm xs]) :=
    headTransport (iterateState p F) out w (suc (functionRemaining child)) ![initialTerm xs] witness before
  exact shiftEarly p F (initialTerm xs) (initialTerm ys) (functionRemaining child) out tick late

#print axioms exact_OpenAuxiliaryRemainingChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunChildProof
