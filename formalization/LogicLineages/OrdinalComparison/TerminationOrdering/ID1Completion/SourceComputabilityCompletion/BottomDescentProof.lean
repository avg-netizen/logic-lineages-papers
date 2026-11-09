module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.BottomRepresentative SourceComputabilityCompletion.BottomDescent
open SourceComputabilityCompletion.BottomDescentSyntaxProof SourceComputabilityCompletion.BottomDescentStepProof
open SourceComputabilityCompletion.BottomDescentInductionProof
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
    Nonempty (Derivation body Gamma ((bottomGraph indicator out).iff (bottomGraph indicator input))) := by
  apply programCases bottomTest (Fin.cons input Fin.elim0) _
  intro β j Delta value hj hv
  rw [SourceComputabilityCompletion.BottomRepresentativeInternalProof.bottomIffRename]
  have hv' : Nonempty (Derivation body Delta (bottomGraph value (input.relabel j))) := by
    simpa only [bottomGraph,graph1,consTermRename,emptyRename] using hv
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hr' := renameInto hr j Delta hj
  rw [parameterRepeatRename] at hr'
  have hout := repeatForward data window (count.relabel j) (input.relabel j) (out.relabel j)
    (parameter.relabel j) value hr' ha' hv'
  exact SourceComputabilityCompletion.BottomRepresentativeInternalProof.indicatorIff bottomTest
    (indicator.relabel j) (out.relabel j) (input.relabel j) value value hout hv' ⟨refl value⟩

theorem selectedIff (data : Data) (window : Program 1) (out input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.representative (readyData data window)) out input parameter))) :
    Nonempty (Derivation body Gamma ((bottomGraph indicator out).iff (bottomGraph indicator input))) := by
  have hv := andRight (activeFactors data window input parameter ha)
  have hn := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    (representative data window) (selectedValidity data window) out input parameter hr hv
  have hrepeat := normalizerRecover (representative data window) (selectedValidity data window)
    out input parameter hn
  exact repeatIff data window out (suc input) input parameter indicator ha hrepeat

theorem actualParameterizedBottomIterationPreservation :
    BottomDescentTargets.ActualParameterizedBottomIterationPreservation := by
  intro body data window α Delta out count input parameter indicator
  let A := activeGraph data window input parameter
  let R := repeatGraph (step data window) out count input parameter
  obtain ⟨d⟩ := repeatIff (body := body) (Gamma := R :: A :: Delta)
    data window out count input parameter indicator
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem actualParameterizedSelectedBottomPreservation :
    BottomDescentTargets.ActualParameterizedSelectedBottomPreservation := by
  intro body data window α Delta out input parameter indicator
  let A := activeGraph data window input parameter
  let R := graph2 (InternalOriginalUniformDescentSelection.representative (readyData data window)) out input parameter
  obtain ⟨d⟩ := selectedIff (body := body) (Gamma := R :: A :: Delta)
    data window out input parameter indicator
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentProof
