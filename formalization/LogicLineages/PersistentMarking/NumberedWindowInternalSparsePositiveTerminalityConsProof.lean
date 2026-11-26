module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityConsShiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityFuelProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalSquareRootArithmeticSupportProof (strictWeakTrans)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePairChecks (exact_OpenFieldConsTailDecrease)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords coordsRename)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveLoop moveFuel)
open NumberedWindowInternalSparsePositiveTerminalityTargets (uniformAt terminalScratch)
open NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof (terminalRename)
open NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof (uniformRename atFuel)
open NumberedWindowInternalSparsePositiveTerminalityConsShiftProof (shiftCons)
open NumberedWindowInternalSparsePositiveTerminalityFuelProof (fuelSuccessorCases)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem chooseAdvanced (raw : Program 5) (least : Program 3)
    (out pred ctx ty current cert hd tl : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (tailBound : Nonempty (Derivation body Γ (ltF tl (suc pred))))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tl))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  apply programCases (advance raw least) (coords ctx ty current hd) (terminalScratch out)
  intro β j Δ next hJ advanced
  rw [terminalRename]
  rw [coordsRename] at advanced
  have l := moveLoop j Δ hJ raw least out (suc pred) ctx ty current cert loop
  rw [sucRelabel] at l
  have cell' := renameInto cell j Δ hJ
  rw [consGraphRename] at cell'
  have ih' := renameInto ih j Δ hJ
  rw [uniformRename] at ih'
  have b := renameInto tailBound j Δ hJ
  rw [orderRename,sucRelabel] at b
  have newLoop := shiftCons raw least (out.relabel j) (pred.relabel j) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (hd.relabel j) (tl.relabel j) next l cell' advanced
  obtain ⟨rule⟩ := atFuel raw least (ctx.relabel j) (ty.relabel j) (tl.relabel j) (pred.relabel j)
    next (out.relabel j) ih'
  obtain ⟨bb⟩ := b
  obtain ⟨ll⟩ := newLoop
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction bb ll)⟩

theorem fromCons (raw : Program 5) (least : Program 3)
    (out fuel ctx ty current cert hd tl : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF cert (suc fuel))))
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out fuel ctx ty current cert)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tl))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  obtain ⟨ordered⟩ := closedApply (exact_OpenFieldConsTailDecrease body α cert hd tl) cell
  rw [equalEqn] at ordered
  have nz : Nonempty (Derivation body Γ (eqn cert z).not) := ⟨Derivation.conjunctionLeft ordered⟩
  have less : Nonempty (Derivation body Γ (ltF tl cert)) := ⟨Derivation.conjunctionRight ordered⟩
  apply fuelSuccessorCases cert fuel (terminalScratch out) bound nz
  intro β j Δ pred hJ eq nowBound
  rw [terminalRename]
  have l := moveLoop j Δ hJ raw least out fuel ctx ty current cert loop
  have d := moveFuel raw least (out.relabel j) (fuel.relabel j) (suc pred) (ctx.relabel j)
    (ty.relabel j) (current.relabel j) (cert.relabel j) eq l
  have c := renameInto cell j Δ hJ
  rw [consGraphRename] at c
  have i := renameInto ih j Δ hJ
  rw [uniformRename] at i
  have m := renameInto less j Δ hJ
  rw [orderRename] at m
  have b := strictWeakTrans (tl.relabel j) (cert.relabel j) (suc pred) m nowBound
  exact chooseAdvanced raw least (out.relabel j) pred (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (hd.relabel j) (tl.relabel j) d c b i

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityConsProof
