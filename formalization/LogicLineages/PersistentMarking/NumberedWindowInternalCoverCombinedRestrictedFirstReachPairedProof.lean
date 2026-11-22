module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachPairedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof (exact_OpenCoverCombinedRestrictedPairedCrossCover)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachProof (exact_OpenCoverFirstReach)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachTargets

theorem exact_OpenCoverCombinedRestrictedPairedFirstReach : ExactOpenCoverCombinedRestrictedPairedFirstReach := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal P W D X a b syn types argument fg gf ma mb k
  apply exact_OpenCoverCombinedRestrictedPairedCrossCover V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal
    syn types argument fg gf ma mb
  intro β i Δ vertices keep0 cover edge
  apply exact_OpenCoverFirstReach (edge4 X W) body β Δ (ctx.relabel i) (cod.relabel i) vertices
    (a.relabel i) (b.relabel i) (goal.relabel i) cover.memberA cover.memberB edge
  intro γ j Θ before after keep1 reports
  have ca := renameInto cover.optionA j Θ keep1
  have cb := renameInto cover.optionB j Θ keep1
  simp only [unaryRename,sucRelabel,Term.relabel_relabel] at ca cb
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel (j ∘ i) ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  rw [formulaRelabelComposition]
  exact k γ (j ∘ i) Θ (vertices.relabel j) before after keep ca cb (by
    simpa only [Term.relabel_relabel] using reports)

#print axioms exact_OpenCoverCombinedRestrictedPairedFirstReach
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachPairedProof
