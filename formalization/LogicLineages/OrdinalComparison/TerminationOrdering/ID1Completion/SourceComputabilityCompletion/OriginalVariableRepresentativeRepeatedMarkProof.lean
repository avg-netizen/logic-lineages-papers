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

theorem repeatIff (data : Data) (window : Program 1) (out count input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data window) out count input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph indicator out).iff (markGraph indicator input))) := by
  apply programCases variableMark (Fin.cons input Fin.elim0) _
  intro β j Delta value hj hv
  rw [OriginalVariableRepresentativeGuardProof.markIffRename]
  have hv' : Nonempty (Derivation body Delta (markGraph value (input.relabel j))) := by
    simpa only [markGraph,graph1,consTermRename,emptyRename] using hv
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hr' := renameInto hr j Delta hj
  rw [parameterRepeatRename] at hr'
  have hout := repeatForward data window (count.relabel j) (input.relabel j) (out.relabel j)
    (parameter.relabel j) value hr' ha' hv'
  exact SourceComputabilityCompletion.BottomRepresentativeInternalProof.indicatorIff variableMark
    (indicator.relabel j) (out.relabel j) (input.relabel j) value value hout hv' ⟨refl value⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
