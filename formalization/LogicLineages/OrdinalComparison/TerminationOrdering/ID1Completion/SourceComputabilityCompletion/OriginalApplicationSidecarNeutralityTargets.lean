module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual raw-combine sidecar preserves and reflects every symbolic value
of the original function-neutrality observer, with nonapplications masked by
the original neutralTest. Window, source type and parameter remain explicit.
No invariant, child output, calibration or fixedness is assumed. -/
def ActualOriginalApplicationSidecarNeutrality : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter value : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
          (OriginalApplicationSidecar.originalData data window) input typ parameter ⊓
        InternalApplicationCertificateConstructors.graph2
          (OriginalApplicationSidecar.fold data window) out input parameter)).imp
      ((OriginalFunctionNeutrality.markGraph value out).iff
        (OriginalFunctionNeutrality.markGraph value input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityTargets
