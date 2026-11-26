module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME raw-combine sidecar preserves actual source validity and the
original raw type, and does not increase the original packed value. All
parameters/contexts are arbitrary. No accepted-window, calibration, child
success, membership, invariant or fixedness hypothesis is supplied. -/
def ActualOriginalApplicationSidecarOutputInvariant : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((InternalParameterizedCanonicalResultFold.sourcePremises
        (originalData data window) input typ parameter ⊓
      InternalApplicationCertificateConstructors.graph2 (fold data window) out input parameter).imp
      (InternalApplicationCertificateConstructors.graph2
          (InternalOriginalUniformDescentSelection.validity (originalData data window))
            InternalOriginalStepGuard.one out parameter ⊓
        (InternalApplicationCertificateConstructors.graph1 InternalUnpair.left typ out ⊓
          InternalParameterizedBoundedDescentNormalizer.atMost out input))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantTargets
