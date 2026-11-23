module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachCrossCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFirstReachProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverCombinedRestrictedFirstReachProof (exact_OpenCoverFirstReach)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
  (exact_OpenCoverCombinedRestrictedMeasuredPairedEdge)
open NumberedWindowInternalCombinedMeasuredFirstReachTargets

theorem exact_InstalledMeasuredFirstReach : ExactInstalledMeasuredFirstReach := by
  intro s V TV M M0 B T base body α Γ ctx ty a b goal K edge use
  apply exact_InstalledMeasuredCrossCover s V TV M M0 B T base body α Γ ctx ty a b goal edge
  intro β i Δ vertices keep0 cover admitted
  apply exact_OpenCoverFirstReach K.edge body β Δ (ctx.relabel i) (ty.relabel i) vertices
    (a.relabel i) (b.relabel i) (goal.relabel i) cover.memberA cover.memberB admitted
  intro γ j Θ before after keep1 reports
  have ca := renameInto cover.optionA j Θ keep1
  have cb := renameInto cover.optionB j Θ keep1
  simp only [unaryRename,sucRelabel,Term.relabel_relabel] at ca cb
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel (j ∘ i) ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  rw [formulaRelabelComposition]
  exact use γ (j ∘ i) Θ (vertices.relabel j) before after keep ca cb
    (by simpa only [Term.relabel_relabel] using reports)

theorem exact_InstalledMeasuredApplicationFirstReach : ExactInstalledMeasuredApplicationFirstReach := by
  intro s V TV M M0 B T base body α Γ ctx dom cod f g arg goal K syn typed argument edge use
  have lifted := exact_OpenCoverCombinedRestrictedMeasuredPairedEdge V TV M M0 B T base s body α Γ
    ctx dom cod f g arg syn typed argument edge
  exact exact_InstalledMeasuredFirstReach s V TV M M0 B T base body α Γ ctx cod _ _ goal lifted use

end LogicLineages.PersistentMarking.NumberedWindowInternalCombinedMeasuredFirstReachProof
