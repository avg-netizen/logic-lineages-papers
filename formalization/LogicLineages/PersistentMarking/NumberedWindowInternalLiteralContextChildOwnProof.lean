module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralContextChildOwnProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addSucc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (orderCases)
open ID1Completion.InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawRun (iterateState ownRun)
open NumberedWindowInternalSparseRawRunShiftProof (shiftEarly)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm ownLoop)
open NumberedWindowInternalSparseRawRunSuccessProof (ownRunTerminal)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt)
open NumberedWindowInternalLiteralDescendingTickSupportProof (tickRename)
open NumberedWindowInternalLiteralDescendingFirstTickProof (FrameDecoder)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralExcessTerminalProof (LitRun TerminalOne runRename)
open NumberedWindowInternalLiteralFuelInductionProof (exact_OpenTrimmedOwnRunWith)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A successful parent run with an actual first contextual tick yields
the real child at its own certificate fuel. The strictly smaller bound
comes from the honest context decoder (including lambda). -/
theorem exact_OpenContextChildOwnRun (P F : Program 3) (decode : FrameDecoder F)
    (q w r a child b : OTerm α)
    (step : D B Γ (TickAt P F z (frameValueTerm a child b) q w r))
    (smaller : D B Γ (ltF child w))
    (accepted : D B Γ (bit (ownRun P F) ![q,w,r])) :
    D B Γ (bit (ownRun P F) ![a,child,b]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  have parent : D B Γ (LitRun P F TerminalOne w q w r) :=
    ownLoop P F TerminalOne xs (ownRunTerminal P F z xs accepted)
  apply orderCases Γ child w _ smaller
  intro β j Δ gap keep e
  let q' := q.relabel j
  let w' := w.relabel j
  let r' := r.relabel j
  let a' := a.relabel j
  let c' := child.relabel j
  let b' := b.relabel j
  let fuel := add c' gap
  obtain ⟨eq⟩ := e
  have atFuel := trans (symm eq) (addSucc c' gap)
  have held := renameInto parent j Δ keep
  simp only [runRename,stateRename,sucRelabel,zRelabel] at held
  have terminal : D B Δ (LitRun P F TerminalOne (suc fuel) q' w' r') :=
    headTransport (iterateState P F) TerminalOne w' (suc fuel)
      ![initialTerm (![q',w',r'] : Fin 3 → OTerm β)] ⟨atFuel⟩ held
  have first := renameInto step j Δ keep
  simp only [tickRename,zRelabel,frameValueTerm,sucRelabel,rawConsRename] at first
  have tail : D B Δ (LitRun P F TerminalOne fuel a' c' b') :=
    shiftEarly P F (initialTerm (![q',w',r'] : Fin 3 → OTerm β)) (initialTerm (![a',c',b'] : Fin 3 → OTerm β))
      fuel TerminalOne first terminal
  simp only [bit,programRename,tripleInputsRename,sucRelabel,zRelabel]
  exact exact_OpenTrimmedOwnRunWith P F decode a' c' b' gap tail

#print axioms exact_OpenContextChildOwnRun
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralContextChildOwnProof
