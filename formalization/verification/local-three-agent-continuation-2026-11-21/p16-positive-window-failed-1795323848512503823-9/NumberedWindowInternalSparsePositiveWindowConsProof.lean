module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords coordsRename)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveChosenConsTargets (genuineHead)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph)
open NumberedWindowInternalSparsePositiveDeadCurrentChecks (exact_OpenNoCurrentFinishZero)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePositiveWindowTargets
open NumberedWindowInternalSparsePositiveWindowMotiveProof
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tailAt (raw : Program 5) (least : Program 3) (ctx ty source cert target h t n : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert h t)))
    (whole : Nonempty (Derivation body Γ (finishAt raw least ctx ty source cert target)))
    (next : Nonempty (Derivation body Γ (selectedGraph raw least n ctx ty (suc source) h))) :
    Nonempty (Derivation body Γ (finishGraph raw least (suc target) ctx ty n t)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := next
  have head : Nonempty (Derivation body Γ (genuineHead raw least ctx ty (suc source) cert h t n)) :=
    ⟨Derivation.conjunctionIntroduction c a⟩
  obtain ⟨rule⟩ := closedApply (exact_OpenFinishCons body raw least α (suc target) ctx ty (suc source) cert h t n) head
  obtain ⟨f⟩ := whole
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft rule) f⟩

theorem fromCons (raw : Program 5) (least W : Program 3) (law : AdvanceWindows raw least W)
    (ctx ty source cert target h t : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert h t)))
    (whole : Nonempty (Derivation body Γ (finishAt raw least ctx ty source cert target)))
    (hyp : Nonempty (Derivation body Γ (safe raw least W ctx ty t target))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty target)) := by
  apply optionGraphCases (advance raw least) (coords ctx ty (suc source) h) _
  · intro β j Δ keep absent
    rw [windowRename]
    rw [coordsRename,sucRelabel] at absent
    have c := renameInto cell j Δ keep
    rw [consGraphRename] at c
    have f := renameInto whole j Δ keep
    rw [finishAtRename] at f
    have rest := tailAt raw least _ _ _ _ _ _ _ z c f absent
    obtain ⟨dead⟩ := exact_OpenNoCurrentFinishZero body raw least β (ctx.relabel j) (ty.relabel j) (t.relabel j)
    obtain ⟨eq⟩ := valueUnique (finish raw least) (suc (target.relabel j)) z
      (args4 (ctx.relabel j) (ty.relabel j) z (t.relabel j)) rest ⟨weakenClosed dead Δ⟩
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ next keep accepted
    rw [windowRename]
    rw [coordsRename,sucRelabel] at accepted
    have c := renameInto cell j Δ keep
    rw [consGraphRename] at c
    have f := renameInto whole j Δ keep
    rw [finishAtRename] at f
    have old := renameInto hyp j Δ keep
    rw [safeRename] at old
    obtain ⟨rest⟩ := tailAt raw least _ _ _ _ _ _ _ (suc next) c f accepted
    obtain ⟨step⟩ := law body β Δ (ctx.relabel j) (ty.relabel j) (source.relabel j) (h.relabel j) next
    obtain ⟨a⟩ := accepted
    have guard := Derivation.conjunctionRight (Derivation.implicationElimination step a)
    obtain ⟨ih⟩ := applyAt raw least W (ctx.relabel j) (ty.relabel j) next (t.relabel j) (target.relabel j) old
    exact ⟨Derivation.implicationElimination ih (Derivation.conjunctionIntroduction guard rest)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowConsProof
