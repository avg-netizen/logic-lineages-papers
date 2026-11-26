module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual raw-combine sidecar preserves and reflects every symbolic value
of the original variable mark: whole raw variable values are encoded, while
nonvariables have mark zero. Original window, source type and parameter remain.
No invariant, child output, calibration or fixedness is assumed. -/
def ActualOriginalApplicationSidecarVariableMark : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter value : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises
          (OriginalApplicationSidecar.originalData data window) input typ parameter ⊓
        InternalApplicationCertificateConstructors.graph2
          (OriginalApplicationSidecar.fold data window) out input parameter)).imp
      ((OriginalVariableRepresentative.markGraph value out).iff
        (OriginalVariableRepresentative.markGraph value input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkTargets
