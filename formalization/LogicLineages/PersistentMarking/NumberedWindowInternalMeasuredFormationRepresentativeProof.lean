module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalApplicationFormationInterfaceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRepresentativeEqualityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredFormationRepresentativeProof
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
open NumberedWindowInternalMeasuredUnrestrictedRepresentativeEqualityProof (exact_OpenMeasuredRepresentativeApplication)
open NumberedWindowInternalOriginalApplicationFormationInterfaceProof
open NumberedWindowInternalThinFormationRepresentativeTargets
open NumberedWindowInternalThinFormationRepresentativeSyntaxProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OriginalParentClosureFromFormation (W : Program 3) (ctx dom cod arg : OTerm α)
    (held : Nonempty (Derivation B Γ (formation W ctx dom cod arg))) :
    OriginalParentClosureAt W B Γ ctx dom cod arg := by
  intro β j Δ f keep typed
  have h := renameInto held j Δ keep
  rw [formationRename] at h
  obtain ⟨h⟩ := h
  obtain ⟨rule⟩ := atFunction W (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) f h
  obtain ⟨typed⟩ := typed
  exact ⟨Derivation.implicationElimination rule typed⟩

/-- The real arithmetic formation formula is enough for the measured
same-body representative rule, with no new caller exchange or class law. -/
theorem exact_OriginalMeasuredFormationRepresentative
    (s : Settings) (base : Program 2) (V baseM : Program 1) (P : Program 2) (G baseW : Program 3) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    RepresentativeAt C s X W := by
  intro M C W X body α Γ ctx dom cod arg f repr value initial chosen final
  let input := formation W ctx dom cod arg ⊓ (initial ⊓ chosen)
  let Δ := input :: Γ
  have d : Derivation body Δ input := Derivation.hypothesis List.mem_cons_self
  have close := exact_OriginalParentClosureFromFormation W ctx dom cod arg ⟨Derivation.conjunctionLeft d⟩
  have windows := exact_ParentWindowsFromOriginalClosure W X ctx dom cod arg close
  obtain ⟨g⟩ := exact_OpenMeasuredRepresentativeApplication s base V baseM P G baseW ctx dom cod f repr arg value
    windows ⟨Derivation.conjunctionRight (Derivation.conjunctionRight d)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight d)⟩
  exact ⟨Derivation.implicationIntroduction g⟩

#print axioms exact_OriginalParentClosureFromFormation
#print axioms exact_OriginalMeasuredFormationRepresentative
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredFormationRepresentativeProof
