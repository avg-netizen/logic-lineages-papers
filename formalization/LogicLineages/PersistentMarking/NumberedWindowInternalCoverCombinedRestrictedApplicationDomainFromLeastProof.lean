module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedUnitFromCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromLeastProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedMeasureBase)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast hasRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof (exact_OpenCoverRefinedAuxSyntaxIntro)
open NumberedWindowInternalCoverRefinedUnitFromCoverProof (exact_OpenRefinedUnitFromPackedLeast)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof (exact_OpenCoverThinMatchingWindowInputs)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof (exact_OpenCoverThinMatchingContextTransport)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalSettingsGrammarGuardOpenProof (exact_OpenSettingsRefitGuardReports)
open NumberedWindowInternalCoverAuxLeastFromSeedLeastsTargets (ActualAuxSeedInputs)
open NumberedWindowInternalCoverAuxLeastFromSeedLeastsProof (exact_OpenCoverAuxLeastFromSeedLeasts)
open NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromLeastTargets

private abbrev sharedBase (M M0 : Program 1) : Program 1 :=
  let A := argumentMeasure (namedSharedMeasure M0)
  fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)

theorem exact_OpenCoverCombinedApplicationDomainFromLeast : ExactOpenCoverCombinedApplicationDomainFromLeast := by
  intro V TV M M0 B T X s body α Γ ctx dom cod fn arg fx P W syn types argument held
  let key := auxiliaryTerm dom cod fn arg
  let R := sharedBase M M0
  have fV := exact_OpenRefinedUnitFromPackedLeast V TV (selectedMeasure P.R) X W s ctx
    (NumberedWindowInternalSparsePathEnvelopeTargets.rawCons dom cod) fn fx held
  have ar := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx dom arg argument
  obtain ⟨syn⟩ := syn
  obtain ⟨f⟩ := fV
  obtain ⟨a⟩ := ar.valid
  have valid := exact_OpenCoverRefinedAuxSyntaxIntro V TV body α Γ dom cod fn arg
    ⟨Derivation.conjunctionIntroduction syn (Derivation.conjunctionIntroduction f a)⟩
  have parsed := exact_OpenCoverThinMatchingContextTransport body α Γ ctx dom arg cod key ar.context
  obtain ⟨typeFacts⟩ := types
  obtain ⟨domLaw⟩ := exact_OpenSettingsRefitGuardReports s T body α Γ dom
  obtain ⟨codLaw⟩ := exact_OpenSettingsRefitGuardReports s T body α Γ cod
  have kd := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft domLaw)
    (Derivation.conjunctionLeft typeFacts))
  have kc := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft codLaw)
    (Derivation.conjunctionRight typeFacts))
  obtain ⟨report⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ ctx dom arg argument
  apply casesLeast P.cover X W s ctx dom arg _ ⟨Derivation.conjunctionRight report⟩
  intro β j Δ ax keep argLeast
  rw [hasRename,appAuxRename]
  have parsed' := renameInto parsed j Δ keep
  simp only [windowRename,key,appAuxRename] at parsed'
  have held' := renameInto held j Δ keep
  rw [leastRename,rawConsRename] at held'
  have f' := renameInto ⟨f⟩ j Δ keep
  have a' := renameInto ⟨a⟩ j Δ keep
  have val := renameInto valid j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,appAuxRename] at f' a' val
  have kd' := renameInto ⟨kd⟩ j Δ keep
  have kc' := renameInto ⟨kc⟩ j Δ keep
  simp only [graphRename,numeralRename] at kd' kc'
  have paid : ActualAuxSeedInputs P.V R X W s body Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j)
      (fn.relabel j) (arg.relabel j) (fx.relabel j) ax :=
    ⟨parsed',held',argLeast,f',a',val,kd',kc'⟩
  exact exact_OpenCoverAuxLeastFromSeedLeasts P.V R X W s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) (fx.relabel j) ax paid

#print axioms exact_OpenCoverCombinedApplicationDomainFromLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromLeastProof
