module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExcessTerminalProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelArithmeticProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport outputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans addSucc)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderProof (congAddRight)
open ID1Completion.InternalAdditionLawsProof (add congAddLeft leftSuccessor associativity)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseRawTick (rootTest)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (ownRun iterateState)
open NumberedWindowInternalSparseRawRunTerminalChecks (exact_OpenRawTerminalLoop)
open NumberedWindowInternalSparseRawRunShiftProof (shiftLate)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm loopOwn)
open NumberedWindowInternalLiteralRunTerminalFlagProof (flagRead)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases)
open NumberedWindowInternalLiteralFirstTickAllCasesProof (TickAt)
open NumberedWindowInternalLiteralDescendingTickSupportProof (tickRename)
open NumberedWindowInternalLiteralExcessTerminalProof
  (LitRun TerminalOne exact_OpenTerminalFirstTickFromFuel)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem expandExcess (before child gap k : OTerm α)
    (e : D B Γ (eqn (add child (suc gap)) before)) :
    D B Γ (eqn (add before k) (suc (add child (add gap k)))) := by
  obtain ⟨de⟩ := e
  exact ⟨trans (congAddRight k (symm de))
    (trans (associativity child (suc gap) k)
      (trans (congAddLeft child (leftSuccessor gap k)) (addSucc child (add gap k))))⟩

/-- Once the actual root has terminated with the unit flag at an
arbitrary fuel, it also does so on its own actual positive witness code.
The root header itself exposes the required predecessor. -/
theorem exact_OpenRootOwnFromExcess (p other : Program 3) (q w r flag fuel : OTerm α)
    (tag : D B Γ (bit rootTest ![q,w,r]))
    (tick : D B Γ (TickAt p other flag z q w r))
    (held : D B Γ (LitRun p other TerminalOne fuel q w r)) :
    D B Γ (bit (ownRun p other) ![q,w,r]) := by
  let goal := bit (ownRun p other) ![q,w,r]
  have unit := exact_OpenTerminalFirstTickFromFuel p other q w r flag fuel tick held
  apply nodeAtCases 0 1 1 ![q,w,r] goal tag
  intro β j Δ values keep arity shaped _
  rcases values with _ | ⟨v,_ | ⟨unexpected,rest⟩⟩
  · simp at arity
  · let q' := q.relabel j
    let w' := w.relabel j
    let r' := r.relabel j
    let c := flag.relabel j
    let xs : Fin 3 → OTerm β := ![q',w',r']
    let before := initialTerm xs
    let after := stateTerm c z
    let n := pairTerm z (rawCons v z)
    have witness : D B Δ (eqn w' (suc n)) := shaped
    obtain ⟨we⟩ := witness
    have t := renameInto tick j Δ keep
    rw [tickRename,zRelabel] at t
    obtain ⟨tail⟩ := exact_OpenRawTerminalLoop B p other β c n
    have later := shiftLate p other before after n after t ⟨weakenClosed tail Δ⟩
    have run := headTransport (iterateState p other) after (suc n) w' ![before] ⟨symm we⟩ later
    have state := loopOwn p other after xs run
    have result := flagRead p other c z xs state
    have u := renameInto unit j Δ keep
    rw [ID1Completion.InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel,zRelabel] at u
    have exactResult := outputTransport (ownRun p other) c (suc z) xs u result
    simp only [goal,bit,ID1Completion.InternalControlGraphSupportProof.programRename,
      NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename,sucRelabel,zRelabel]
    exact exactResult
  · simp at arity

#print axioms expandExcess
#print axioms exact_OpenRootOwnFromExcess
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelArithmeticProof
