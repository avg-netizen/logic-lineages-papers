module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionAllocationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanChooseFiltersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionAllocationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)
open NumberedWindowInternalOriginScanChooseFiltersProof (exact_OriginalChooseCertifiedFilters)
open NumberedWindowInternalOriginScanInductionSyntaxProof (renamePools filterRename)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalProjectedCountCasesProof (exact_OpenProjectedCountCases)
open NumberedWindowInternalProjectedCountCasesTargets (Inputs)
open NumberedWindowInternalProjectedCountInductionSyntaxProof (projectRename)
open NumberedWindowInternalOriginInsertionAllocationTargets

/-- Allocate both actual inserted tapes and expose both certified scans
and exact projected multiplicity simultaneously, holding every physical
and raw removed pool report fixed. -/
theorem exact_OpenOriginInsertionAllocation : ExactOpenOriginInsertionAllocation := by
  intro r B α Γ rows removed decoded rawL rawR scratchL scratchR joinedRemoved full goal
    pools original wholeProjected next
  apply exact_OriginalChooseCertifiedFilters r rows removed decoded rawL rawR scratchL scratchR
    joinedRemoved goal pools original
  intro β j Δ outL outR keep fL fR loopL loopR
  have full' := renameInto wholeProjected j Δ keep
  rw [projectRename] at full'
  have here : Inputs r B Δ (rows.relabel j) (scratchL.relabel j) outL outR
      (rawL.relabel j) (rawR.relabel j) (full.relabel j) :=
    ⟨fL,fR,loopL,loopR,full'⟩
  apply exact_OpenProjectedCountCases r B β Δ (rows.relabel j) (scratchL.relabel j)
    outL outR (rawL.relabel j) (rawR.relabel j) (full.relabel j) (goal.relabel j) here
  intro γ k Ω pL pR joinedProjected keep' mapL mapR app obs
  let ρ := k ∘ j
  have survive := keepThrough j k keep keep'
  have fL' := renameInto fL k Ω keep'
  have fR' := renameInto fR k Ω keep'
  have loopL' := renameInto loopL k Ω keep'
  have loopR' := renameInto loopR k Ω keep'
  rw [filterRename] at fL' fR'
  rw [loopRename] at loopL' loopR'
  rw [formulaRelabelComposition]
  exact next γ ρ Ω (outL.relabel k) (outR.relabel k) pL pR joinedProjected survive
    ⟨renamePools pools ρ survive,
     by simpa only [ρ,Term.relabel_relabel] using fL',
     by simpa only [ρ,Term.relabel_relabel] using fR',
     by simpa only [ρ,Term.relabel_relabel] using loopL',
     by simpa only [ρ,Term.relabel_relabel] using loopR',
     mapL,mapR,app,by simpa only [ρ,Term.relabel_relabel] using obs⟩

#print axioms exact_OpenOriginInsertionAllocation

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionAllocationProof
