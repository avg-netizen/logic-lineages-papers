module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual raw-combine sidecar preserves and reflects every symbolic value
of the original exact same-type bottom test, not merely a root-tag predicate.
Original window, source type and parameter remain explicit. No invariant,
child output, Boolean-range, calibration or fixedness premise is assumed. -/
def ActualOriginalApplicationSidecarBottomTest : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter value : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
          (OriginalApplicationSidecar.originalData data window) input typ parameter ⊓
        InternalApplicationCertificateConstructors.graph2
          (OriginalApplicationSidecar.fold data window) out input parameter)).imp
      ((BottomRepresentative.bottomGraph value out).iff
        (BottomRepresentative.bottomGraph value input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestTargets
