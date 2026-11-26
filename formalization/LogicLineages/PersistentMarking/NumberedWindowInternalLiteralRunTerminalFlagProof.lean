module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunTerminalChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRunTerminalFlagProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue recursionZeroValue projectionValue headTransport valueUnique programRename zeroSuccessorCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename)
open NumberedWindowInternalSparseRawRun (iterateState step ownState ownRun)
open NumberedWindowInternalSparseRawRunTerminalChecks (exact_OpenRawTerminalLoop)
open NumberedWindowInternalSparseRawRunSuccessProof (headRead)
open NumberedWindowInternalSparseRawRunShiftProof (shiftLate)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm loopOwn)

abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem starterRename {β : Type} (q w r : OTerm α) (j : α → β) :
    (initialTerm (![q,w,r] : Fin 3 → OTerm α)).relabel j =
      initialTerm (![q.relabel j,w.relabel j,r.relabel j] : Fin 3 → OTerm β) := by
  simp only [initialTerm,stateRename,frameValueTerm,sucRelabel,rawConsRename,zRelabel]
  rfl

theorem flagRead (p other : Program 3) (flag frame : OTerm α) (xs : Fin 3 → OTerm α)
    (h : D B Γ (programGraph (ownState p other) (stateTerm flag frame) xs)) :
    D B Γ (programGraph (ownRun p other) flag xs) := by
  apply compositionValue cellHead (fun _ : Fin 1 => ownState p other) flag xs ![stateTerm flag frame]
    (headRead flag frame)
  intro i
  obtain rfl := Fin.eq_zero i
  exact h

/-- An original raw own-run with a terminal first tick can only accept
with the first tick's actual flag. Zero fuel initially reads zero and
is ruled out, not assumed numerically positive. -/
theorem exact_OpenTerminalFirstTickFlag (p other : Program 3) (q w r flag : OTerm α)
    (tick : D B Γ (programGraph (chosenTick p other) (stateTerm flag z)
      ![initialTerm (![q,w,r])]))
    (success : D B Γ (programGraph (ownRun p other) (suc z) ![q,w,r])) :
    D B Γ (eqn flag (suc z)) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let start := initialTerm xs
  apply zeroSuccessorCases Γ w (eqn flag (suc z))
  · let Δ := eqn w z :: Γ
    have base : D B Δ (programGraph (iterateState p other) start ![z,start]) :=
      recursionZeroValue (.projection 0) (step p other) start ![start] (projectionValue 0 ![start])
    have zw : D B Δ (eqn z w) := ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩
    have savedRun : D B Δ (programGraph (iterateState p other) start ![w,start]) :=
      headTransport (iterateState p other) start z w ![start] zw base
    have same := loopOwn p other start xs savedRun
    have flagZero := flagRead p other z (frameValueTerm q w r) xs same
    obtain ⟨hs⟩ := success
    obtain ⟨absurd⟩ := valueUnique (ownRun p other) (suc z) z xs ⟨addHyp hs _⟩ flagZero
    exact ⟨Derivation.explosion (sucNeZeroApply absurd)⟩
  · intro β j Δ fuel keep fuelEq
    rw [eqnRelabel,sucRelabel,zRelabel]
    let ys : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
    let before := initialTerm ys
    let after := stateTerm (flag.relabel j) z
    have t := renameInto tick j Δ keep
    rw [programRename,inputsRename,starterRename,stateRename,zRelabel] at t
    obtain ⟨loop⟩ := exact_OpenRawTerminalLoop B p other β (flag.relabel j) fuel
    have later := shiftLate p other before after fuel after t ⟨weakenClosed loop Δ⟩
    obtain ⟨ew⟩ := fuelEq
    have atWitness : D B Δ (programGraph (iterateState p other) after ![w.relabel j,before]) :=
      headTransport (iterateState p other) after (suc fuel) (w.relabel j) ![before] ⟨symm ew⟩ later
    have state := loopOwn p other after ys atWitness
    have value := flagRead p other (flag.relabel j) z ys state
    have accepts := renameInto success j Δ keep
    rw [programRename,tripleInputsRename,sucRelabel,zRelabel] at accepts
    exact valueUnique (ownRun p other) (flag.relabel j) (suc z) ys value accepts

#print axioms exact_OpenTerminalFirstTickFlag
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRunTerminalFlagProof
