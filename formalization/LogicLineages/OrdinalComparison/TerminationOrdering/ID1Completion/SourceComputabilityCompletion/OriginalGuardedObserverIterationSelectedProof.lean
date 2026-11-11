module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverIterationSelectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalGuardedObserverIteration
open SourceComputabilityCompletion.OriginalGuardedObserverIterationSyntaxProof SourceComputabilityCompletion.OriginalGuardedObserverIterationStepProof
open SourceComputabilityCompletion.OriginalGuardedObserverIterationProof
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

theorem repeatIff (data : Data) (closure : Closure data) (supply : Preservation data) (out count input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out count input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph data indicator out).iff (markGraph data indicator input))) := by
  apply programCases data.observer (Fin.cons input Fin.elim0) _
  intro β j Delta value hj hv
  change Nonempty (Derivation body Delta
    (((graph1 data.observer indicator out).relabel j).iff
      ((graph1 data.observer indicator input).relabel j)))
  rw [graph1Rename, graph1Rename]
  have hv' : Nonempty (Derivation body Delta (markGraph data value (input.relabel j))) := by
    simpa only [markGraph,graph1,consTermRename,emptyRename] using hv
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hr' := renameInto hr j Delta hj
  rw [parameterRepeatRename] at hr'
  have hout := repeatForward data closure supply (count.relabel j) (input.relabel j) (out.relabel j)
    (parameter.relabel j) value hr' ha' hv'
  exact SourceComputabilityCompletion.BottomRepresentativeInternalProof.indicatorIff data.observer
    (indicator.relabel j) (out.relabel j) (input.relabel j) value value hout hv' ⟨refl value⟩


theorem selectedIff (data : Data) (validity : Validity data) (closure : Closure data) (supply : Preservation data) (out input parameter indicator : OTerm α)
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hr : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.fallbackRepresentative data.representative data.valid) out input parameter))) :
    Nonempty (Derivation body Gamma ((markGraph data indicator out).iff (markGraph data indicator input))) := by
  have hv := validity body α Gamma input parameter ha
  have hn := InternalOriginalUniformDescentSelectionInternalProof.boundedRecover
    data.representative data.valid out input parameter hr hv
  have hrepeat := normalizerRecover data.representative data.valid
    out input parameter hn
  exact repeatIff data closure supply out (suc input) input parameter indicator ha hrepeat



end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverIterationSelectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalGuardedObserverIterationSelectedProof
