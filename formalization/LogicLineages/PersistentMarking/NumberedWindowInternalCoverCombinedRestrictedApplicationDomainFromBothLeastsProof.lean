module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromBothLeastsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedUnitFromCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedContextFromLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromBothLeastsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedSharedMeasure)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedMeasureBase)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverRefinedAuxSyntaxIntroProof (exact_OpenCoverRefinedAuxSyntaxIntro)
open NumberedWindowInternalCoverRefinedUnitFromCoverProof (exact_OpenRefinedUnitFromPackedLeast)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxContextProof (exact_OpenCoverThinMatchingContextTransport)
open NumberedWindowInternalCoverCombinedRestrictedContextFromLeastProof (exact_OpenCoverContextFromPackedLeast)
open NumberedWindowInternalSettingsGrammarGuardOpenProof (exact_OpenSettingsRefitGuardReports)
open NumberedWindowInternalCoverAuxLeastFromSeedLeastsTargets (ActualAuxSeedInputs)
open NumberedWindowInternalCoverAuxLeastFromSeedLeastsProof (exact_OpenCoverAuxLeastFromSeedLeasts)
open NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromBothLeastsTargets

private abbrev sharedBase (M M0 : Program 1) : Program 1 :=
  let A := argumentMeasure (namedSharedMeasure M0)
  fittedMeasureBase (ordinaryMeasureBase (numberedMeasureBase M A) A)

theorem exact_OpenCoverCombinedApplicationDomainFromBothLeasts : ExactOpenCoverCombinedApplicationDomainFromBothLeasts := by
  intro V TV M M0 B T X s body α Γ ctx dom cod fn arg fx ax P W syn types fnLeast argLeast
  let key := auxiliaryTerm dom cod fn arg
  let R := sharedBase M M0
  have fV := exact_OpenRefinedUnitFromPackedLeast V TV (selectedMeasure P.R) X W s ctx
    (rawCons dom cod) fn fx fnLeast
  have aV := exact_OpenRefinedUnitFromPackedLeast V TV (selectedMeasure P.R) X W s ctx
    dom arg ax argLeast
  obtain ⟨hs⟩ := syn
  obtain ⟨hf⟩ := fV
  obtain ⟨ha⟩ := aV
  have valid := exact_OpenCoverRefinedAuxSyntaxIntro V TV body α Γ dom cod fn arg
    ⟨Derivation.conjunctionIntroduction hs (Derivation.conjunctionIntroduction hf ha)⟩
  have context := exact_OpenCoverContextFromPackedLeast P.cover X W s ctx dom arg ax argLeast
  have parsed := exact_OpenCoverThinMatchingContextTransport body α Γ ctx dom arg cod key context
  obtain ⟨typeFacts⟩ := types
  obtain ⟨domLaw⟩ := exact_OpenSettingsRefitGuardReports s T body α Γ dom
  obtain ⟨codLaw⟩ := exact_OpenSettingsRefitGuardReports s T body α Γ cod
  have kd := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft domLaw)
    (Derivation.conjunctionLeft typeFacts))
  have kc := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft codLaw)
    (Derivation.conjunctionRight typeFacts))
  have paid : ActualAuxSeedInputs P.V R X W s body Γ ctx dom cod fn arg fx ax :=
    ⟨parsed,fnLeast,argLeast,⟨hf⟩,⟨ha⟩,valid,⟨kd⟩,⟨kc⟩⟩
  exact exact_OpenCoverAuxLeastFromSeedLeasts P.V R X W s body α Γ ctx dom cod fn arg fx ax paid

#print axioms exact_OpenCoverCombinedApplicationDomainFromBothLeasts
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedApplicationDomainFromBothLeastsProof
