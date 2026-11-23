module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainClassProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast hasRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationProof (exact_FullyMeasuredClassApplication)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainProof
  (exact_OpenCoverApplicationHasLeastFromWindow)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainTargets

theorem exact_FullyMeasuredClassApplicationDomain : ExactFullyMeasuredClassApplicationDomain := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g x arg goal P W Xm syn types argument wf wg lf lg k
  let af := auxiliaryTerm dom cod f arg
  let ag := auxiliaryTerm dom cod g arg
  have fd := exact_OpenCoverApplicationHasLeastFromWindow V TV M M0 B T Xm s body α Γ
    ctx dom cod f arg syn types argument wf
  have gd := exact_OpenCoverApplicationHasLeastFromWindow V TV M M0 B T Xm s body α Γ
    ctx dom cod g arg syn types argument wg
  apply casesLeast P.cover Xm W s ctx cod af goal fd
  intro β i Δ m keep0 first
  have gDomain := renameInto gd i Δ keep0
  rw [hasRename] at gDomain
  apply casesLeast P.cover Xm W s (ctx.relabel i) (cod.relabel i) (ag.relabel i) (goal.relabel i) gDomain
  intro γ j Θ m' keep1 last
  let r : α → γ := j ∘ i
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel r ∈ Θ := by
    rw [← formulaRelabelComposition]
    exact keep1 _ (keep0 p hp)
  have ff := renameInto first j Θ keep1
  rw [leastRename] at ff
  simp only [Term.relabel_relabel] at ff last
  have ss := renameInto syn r Θ keep
  have ts := renameInto types r Θ keep
  have ar := renameInto argument r Θ keep
  have fl := renameInto lf r Θ keep
  have gl := renameInto lg r Θ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at ss ts
  rw [windowRename] at ar
  rw [leastRename,rawConsRename] at fl gl
  have fTyped := ff
  have gTyped := last
  change Nonempty (Derivation body Θ
    (NumberedWindowInternalSparsePackedLeastOpen.leastGraph P.cover Xm W s
      (ctx.relabel r) (cod.relabel r) (af.relabel r) (m.relabel j))) at fTyped
  change Nonempty (Derivation body Θ
    (NumberedWindowInternalSparsePackedLeastOpen.leastGraph P.cover Xm W s
      (ctx.relabel r) (cod.relabel r) (ag.relabel r) m')) at gTyped
  simp only [af,appAuxRename] at fTyped
  simp only [ag,appAuxRename] at gTyped
  have matched := exact_FullyMeasuredClassApplication V TV M M0 B T base s body γ Θ (ctx.relabel r)
    (dom.relabel r) (cod.relabel r) (f.relabel r) (g.relabel r) (x.relabel r) (arg.relabel r)
    (m.relabel j) m' ss ts ar fl gl fTyped gTyped
  rw [← appAuxRename] at matched
  rw [formulaRelabelComposition]
  exact k γ r Θ (m.relabel j) keep ff matched

#print axioms exact_FullyMeasuredClassApplicationDomain
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredApplicationDomainClassProof
