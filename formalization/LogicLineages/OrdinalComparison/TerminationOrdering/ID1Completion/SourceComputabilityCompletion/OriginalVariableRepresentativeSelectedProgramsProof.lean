module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
open OriginalVariableRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalVariableRepresentativeIteration
open SourceComputabilityCompletion.OriginalVariableRepresentativeIterationSyntaxProof SourceComputabilityCompletion.OriginalVariableRepresentativeStepProof
open SourceComputabilityCompletion.OriginalVariableRepresentativeIterationProof
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
      (SpineApplicationTargets.parameters (OriginalVariableRepresentative.baseData data window) window) window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (selectedValidity data window) := by
  simp only [BottomRepresentative.active,OriginalVariableRepresentativeIteration.selectedValidity,
    SpineApplicationIteration.selectedValidity,BottomDescent.selectedValidity,
    BottomRepresentative.readyData,BottomRepresentative.baseData,
    InternalOriginalUniformContextMembership.normalizeData,
    InternalOriginalUniformDescentSelection.validity]


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
