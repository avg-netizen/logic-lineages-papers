module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalApplicationFormationInterfaceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRepresentativeEqualityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredFormationRepresentativeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredRepresentativeBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredFormationRepresentativeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalRankMeasuredRepresentativeBindingProof (exact_OpenRankMeasuredRepresentativeBinding)
open NumberedWindowInternalMeasuredFormationRepresentativeProof (exact_OriginalParentClosureFromFormation)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalOriginalApplicationFormationInterfaceProof
open NumberedWindowInternalThinFormationRepresentativeTargets
open NumberedWindowInternalThinFormationRepresentativeSyntaxProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The real arithmetic formation formula is enough for the measured
same-body representative rule, with no new caller exchange or class law. -/
theorem exact_OriginalRankMeasuredFormationRepresentative
    (s : Settings) (base : Program 2) (V baseM g : Program 1) (P : Program 2) (G baseW : Program 3) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let R := auxRank g
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s R D
    RepresentativeAt C s X W := by
  intro M C W R D X body α Γ ctx dom cod arg f repr value initial chosen final
  let input := formation W ctx dom cod arg ⊓ (initial ⊓ chosen)
  let Δ := input :: Γ
  have d : Derivation body Δ input := Derivation.hypothesis List.mem_cons_self
  have close := exact_OriginalParentClosureFromFormation W ctx dom cod arg ⟨Derivation.conjunctionLeft d⟩
  have windows := exact_ParentWindowsFromOriginalClosure W X ctx dom cod arg close
  obtain ⟨g⟩ := exact_OpenRankMeasuredRepresentativeBinding s base V baseM g P G baseW ctx dom cod f repr arg value
    windows ⟨Derivation.conjunctionRight (Derivation.conjunctionRight d)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
  exact ⟨Derivation.implicationIntroduction g⟩

#print axioms exact_OriginalRankMeasuredFormationRepresentative
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredFormationRepresentativeProof
