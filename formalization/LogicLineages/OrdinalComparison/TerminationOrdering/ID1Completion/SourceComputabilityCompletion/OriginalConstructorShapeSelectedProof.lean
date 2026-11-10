module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSelectedProof
open OriginalConstructorShape
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalConstructorShapeIteration
open SourceComputabilityCompletion.OriginalConstructorShapeIterationSyntaxProof SourceComputabilityCompletion.OriginalConstructorShapeStepProof
open SourceComputabilityCompletion.OriginalConstructorShapeIterationProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationSyntaxProof
open InternalParameterizedBoundedDescentNormalizerSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Expose only the tuple field, rather than comparing expanded graph ASTs. -/
theorem selectedValidityProgram (data : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.validity (selectedData data window) =
      selectedValidity data window := rfl

theorem selectedRepresentativeProgram (data : Data) (window : Program 1) :
    InternalOriginalUniformDescentSelection.representative (selectedData data window) =
      InternalOriginalUniformDescentSelection.fallbackRepresentative
        (leaf data window) (selectedValidity data window) := rfl
/-- Compare the actual guard Programs before entering their graph formulas. -/
theorem activeProgram (data : Data) (window : Program 1) :
    BottomRepresentative.active
      (SpineApplicationTargets.parameters
        (OriginalVariableRepresentative.baseData (baseData data window) window) window) window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (selectedValidity data window) :=
  OriginalVariableRepresentativeSelectedProof.activeProgram (baseData data window) window

theorem repeatIff (data : Data) (window : Program 1) (out count input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data window) out count input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator input))) := by
  apply programCases mark (Fin.cons input Fin.elim0) _
  intro β j Delta value hj hv
  rw [OriginalConstructorShapeGuardProof.markIffRename]
  have hv' : Nonempty (Derivation body Delta (markGraph value (input.relabel j))) := by
    simpa only [markGraph,graph1,consTermRename,emptyRename] using hv
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hr' := renameInto hr j Delta hj
  rw [parameterRepeatRename] at hr'
  have hout := repeatForward data window (count.relabel j) (input.relabel j) (out.relabel j)
    (parameter.relabel j) value hr' ha' hv'
  exact SourceComputabilityCompletion.BottomRepresentativeInternalProof.indicatorIff mark
    (indicator.relabel j) (out.relabel j) (input.relabel j) value value hout hv' ⟨refl value⟩


theorem selectedIff (data : Data) (window : Program 1) (out input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.representative (selectedData data window)) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator input))) := by
  have hv := andRight (activeFactors data window input parameter ha)
  rw [selectedRepresentativeProgram] at hr
  have hn := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    (leaf data window) (selectedValidity data window) out input parameter hr hv
  have hrepeat := normalizerRecover (leaf data window) (selectedValidity data window)
    out input parameter hn
  exact repeatIff data window out (suc input) input parameter indicator ha hrepeat


/-- The actual window and final validator construct the active guard; no
calibration, assumed invariant or reflected native fact enters the calculus. -/
theorem selectedMarkPreservation (data : Data) (window : Program 1) :
    SelectedMarkPreservation (selectedData data window) window := by
  intro body α Delta out input parameter mark
  let A := windowGraph window input parameter ⊓
    (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window))
      InternalOriginalStepGuard.one input parameter ⊓
      graph2 (InternalOriginalUniformDescentSelection.representative (selectedData data window))
        out input parameter)
  have hp : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw := andLeft hp
  have hv := andLeft (andRight hp)
  have hr := andRight (andRight hp)
  rw [selectedValidityProgram] at hv
  have ha : Nonempty (Derivation body (A :: Delta) (activeGraph data window input parameter)) := by
    unfold OriginalConstructorShapeIteration.activeGraph BottomRepresentative.activeGraph
    rw [activeProgram]
    exact InternalAcceptanceConjunctionProof.conjunctionAccept (BottomRepresentative.windowAt window)
      (selectedValidity data window) ![input,parameter] hw hv
  obtain ⟨d⟩ := selectedIff data window out input parameter mark ha hr
  exact ⟨Derivation.implicationIntroduction d⟩


theorem actualOriginalConstructorShapeSelectedPreservation :
    OriginalConstructorShapeTargets.ActualOriginalConstructorShapeSelectedPreservation := by
  intro data window
  exact selectedMarkPreservation data window

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSelectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSelectedProof
