module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The raw-combine sidecar preserves and reflects the FULL original encoded
bottom flag/spine depth at every symbolic value. Original window, source type
and parameter remain explicit; no induction hypothesis, output invariant,
child-success, calibration or fixedness premise is added. -/
def ActualOriginalApplicationSidecarSpine : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter value : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
          (OriginalApplicationSidecar.originalData data window) input typ parameter ⊓
        InternalApplicationCertificateConstructors.graph2
          (OriginalApplicationSidecar.fold data window) out input parameter)).imp
      ((BottomSpineMeasure.graph value out).iff
        (BottomSpineMeasure.graph value input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineTargets
