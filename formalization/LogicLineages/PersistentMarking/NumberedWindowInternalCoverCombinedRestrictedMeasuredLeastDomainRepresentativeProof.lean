module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredLeastDomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredLeastDomainRepresentativeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof (exact_FullyMeasuredLeastRepresentativeApplication)
open NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromLeastProof
  (exact_OpenCoverCombinedApplicationDomainFromLeast)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredLeastDomainTargets

theorem exact_FullyMeasuredRepresentativeApplicationLeastDomain : ExactFullyMeasuredRepresentativeApplicationLeastDomain := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f x arg goal P W Xm syn types argument fnLeast k
  have seedDomain := exact_OpenCoverCombinedApplicationDomainFromLeast V TV M M0 B T Xm s body α Γ
    ctx dom cod f arg x syn types argument fnLeast
  apply casesLeast P.cover Xm W s ctx cod (auxiliaryTerm dom cod f arg) goal seedDomain
  intro β j Δ actual keep fLeast
  have ss := renameInto syn j Δ keep
  have ts := renameInto types j Δ keep
  have ar := renameInto argument j Δ keep
  have fn := renameInto fnLeast j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at ss ts
  rw [windowRename] at ar
  rw [leastRename,rawConsRename] at fn
  have typedF := fLeast
  rw [appAuxRename] at typedF
  have repr := exact_FullyMeasuredLeastRepresentativeApplication V TV M M0 B T base s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (x.relabel j)
    (arg.relabel j) actual ss ts ar typedF fn
  rw [← appAuxRename] at repr
  exact k β j Δ actual keep fLeast repr

#print axioms exact_FullyMeasuredRepresentativeApplicationLeastDomain
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredLeastDomainRepresentativeProof
