module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual raw-combine sidecar preserves and reflects every symbolic value
of the original root mark (constructor tag and masked application domain).
The original window, source type, context and parameter remain explicit.
No observer invariant, child output, calibration or fixedness is assumed. -/
def ActualOriginalApplicationSidecarRootMark : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter value : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
          (OriginalApplicationSidecar.originalData data window) input typ parameter ⊓
        InternalApplicationCertificateConstructors.graph2
          (OriginalApplicationSidecar.fold data window) out input parameter)).imp
      ((OriginalConstructorShape.markGraph value out).iff
        (OriginalConstructorShape.markGraph value input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkTargets
