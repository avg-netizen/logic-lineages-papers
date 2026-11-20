module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsFuelCompareProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalScratchCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsLoopCompareProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalSquareRootArithmeticSupportProof (orderRight)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairChecks (exact_OpenFieldConsTailDecrease)
open NumberedWindowInternalSparsePairGraphProof (consEquation)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveLoop moveFuel)
open NumberedWindowInternalSparsePositiveTerminalityChecks (exact_OpenChosenFuelTerminal)
open NumberedWindowInternalSparsePositiveTerminalScratchCasesProof (terminalCases)
open NumberedWindowInternalSparsePositiveTerminalityConsShiftProof (shiftCons)
open NumberedWindowInternalSparsePositiveChosenConsFuelCompareProof (compareFuel)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem compareWithTerminal (raw : Program 5) (least : Program 3)
    (left right pred ctx ty next tail : OTerm α)
    (longer : Nonempty (Derivation body Γ (loopGraph raw least left pred ctx ty next tail)))
    (shorter : Nonempty (Derivation body Γ (loopGraph raw least right tail ctx ty next tail)))
    (bound : Nonempty (Derivation body Γ (ltF tail (suc pred)))) :
    Nonempty (Derivation body Γ (eqn left right)) := by
  have done := closedApply (exact_OpenChosenFuelTerminal body raw least α right ctx ty next tail) shorter
  apply terminalCases right (eqn left right) done
  intro β j Δ result hJ terminal
  rw [eqnRelabel]
  have l := moveLoop j Δ hJ raw least left pred ctx ty next tail longer
  have r := moveLoop j Δ hJ raw least right tail ctx ty next tail shorter
  have hb := renameInto bound j Δ hJ
  rw [orderRename,sucRelabel] at hb
  exact compareFuel raw least (left.relabel j) (right.relabel j) (pred.relabel j)
    (ctx.relabel j) (ty.relabel j) (next.relabel j) (tail.relabel j) result l r terminal hb

theorem compareLoops (raw : Program 5) (least : Program 3)
    (left right ctx ty initial cert head tail next : OTerm α)
    (old : Nonempty (Derivation body Γ (loopGraph raw least left cert ctx ty initial cert)))
    (new : Nonempty (Derivation body Γ (loopGraph raw least right tail ctx ty next tail)))
    (cell : Nonempty (Derivation body Γ (consGraph cert head tail)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least next ctx ty initial head))) :
    Nonempty (Derivation body Γ (eqn left right)) := by
  let pred := pairTerm head tail
  obtain ⟨e⟩ := consEquation cert head tail cell
  obtain ⟨b⟩ := closedApply (exact_OpenFieldConsTailDecrease body α cert head tail) cell
  have bound : Nonempty (Derivation body Γ (ltF tail (suc pred))) :=
    ⟨orderRight tail e (Derivation.conjunctionRight b)⟩
  have old' := moveFuel raw least left cert (suc pred) ctx ty initial cert ⟨e⟩ old
  have longer := shiftCons raw least left pred ctx ty initial cert head tail next old' cell advanced
  exact compareWithTerminal raw least left right pred ctx ty next tail longer new bound

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsLoopCompareProof
