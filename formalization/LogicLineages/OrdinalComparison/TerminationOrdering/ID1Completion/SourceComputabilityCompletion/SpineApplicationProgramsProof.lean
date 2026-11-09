module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentTransportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (OTerm)
open SpineApplicationTargets (selectedData parameters)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Stop at the SAME readyData call. Do not unfold its record or Programs. -/
theorem selectedDataEq (data : Data) (window : Program 1) :
    selectedData data window = BottomRepresentative.readyData (parameters data window) window := by
  unfold SpineApplicationTargets.selectedData BottomSource.selection SpineApplicationTargets.parameters
  rfl

/-- The already checked generic validator identity avoids normalizing a
concrete oldR/marker tuple when constructing an actual active graph. -/
theorem abstractActiveValue {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (data : Data) (window : Program 1) (input parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) InternalOriginalStepGuard.one input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (BottomDescent.selectedValidity data window) InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation body Gamma (BottomRepresentative.activeGraph data window input parameter)) := by
  unfold BottomRepresentative.activeGraph BottomRepresentative.active
  rw [← BottomDescentSyntaxProof.selectedValidity_eq data window]
  exact conjunctionAccept (BottomRepresentative.windowAt window)
    (BottomDescent.selectedValidity data window)
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hv

theorem activeValue {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (data : Data) (window : Program 1) (input parameter : OTerm α)
    (hw : Nonempty (Derivation body Gamma
      (graph2 (BottomRepresentative.windowAt window) InternalOriginalStepGuard.one input parameter)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity (selectedData data window))
        InternalOriginalStepGuard.one input parameter))) :
    Nonempty (Derivation body Gamma (SpineApplicationIteration.activeGraph data window input parameter)) := by
  unfold SpineApplicationIteration.activeGraph
  apply abstractActiveValue (parameters data window) window input parameter hw
  unfold BottomDescent.selectedValidity
  rw [← selectedDataEq]
  exact hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationProof
