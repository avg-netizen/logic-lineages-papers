module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedCoreProof
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
    unfold OriginalVariableRepresentativeIteration.activeGraph BottomRepresentative.activeGraph
    rw [activeProgram]
    exact InternalAcceptanceConjunctionProof.conjunctionAccept (BottomRepresentative.windowAt window)
      (selectedValidity data window) ![input,parameter] hw hv
  obtain ⟨d⟩ := selectedIff data window out input parameter mark ha hr
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeSelectedProof
