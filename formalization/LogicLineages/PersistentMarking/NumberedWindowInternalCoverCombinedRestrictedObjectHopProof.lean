module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedObjectHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedObjectHopProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls someHopCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceWitnessProof (reportCases)
open NumberedWindowInternalSparsePathSuccessfulAdvanceChecks (exact_OpenSuccessfulAdvanceCalls)
open NumberedWindowInternalCoverCombinedRestrictedRawHopTargets (thinRawAt)
open NumberedWindowInternalCoverCombinedRestrictedSingletonProof (exact_OpenCoverCombinedRestrictedSingleton)
open NumberedWindowInternalCoverCombinedRestrictedObjectHopTargets

theorem exact_OpenCoverCombinedRestrictedObjectHop : ExactOpenCoverCombinedRestrictedObjectHop := by
  intro V TV M M0 B T root other X s body α Γ ctx dom cod arg current hop target goal
    P W raw least syn types input cell k
  obtain ⟨rule⟩ := exact_OpenSuccessfulAdvanceCalls body raw least α ctx (rawCons dom cod) current hop target
  obtain ⟨cell⟩ := cell
  have report := Derivation.implicationElimination (weakenClosed (Derivation.conjunctionLeft rule) Γ) cell
  apply reportCases raw least ctx (rawCons dom cod) current hop target goal ⟨report⟩
  intro β j Δ q w r keep fields
  rw [rawConsRename] at fields
  have syn' := renameInto syn j Δ keep
  have types' := renameInto types j Δ keep
  have input' := renameInto input j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' types'
  rw [windowRename] at input'
  obtain ⟨hit⟩ := fields
  have step : Nonempty (Derivation body Δ (thinRawAt raw (ctx.relabel j)
      (rawCons (dom.relabel j) (cod.relabel j)) q w r)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hit)⟩
  have single := exact_OpenCoverCombinedRestrictedSingleton V TV M M0 B T root other X s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) q w r (arg.relabel j) syn' types' input' step
  exact k β j Δ q w r keep ⟨hit⟩ single

#print axioms exact_OpenCoverCombinedRestrictedObjectHop
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedObjectHopProof
