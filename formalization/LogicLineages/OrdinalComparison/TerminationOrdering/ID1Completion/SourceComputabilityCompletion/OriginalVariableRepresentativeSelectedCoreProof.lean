module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProgramsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRepeatedMarkProof
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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
