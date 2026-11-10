module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The entire original observer-selection pipeline leaves the actual
sidecar-refined old representative graph unchanged at EVERY input and
parameter. The right side is the original active branch C with the literal
old-representative inactive fallback, not C unconditionally. No native
calibration, validity, observer invariant or fixedness premise is supplied. -/
def ActualOriginalApplicationSidecarGuardRedundancy : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input parameter : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((InternalApplicationCertificateConstructors.graph2
        (selectedData data window).oldRepresentative out input parameter).iff
      (InternalApplicationCertificateConstructors.graph2
        (representative data window) out input parameter)))

/-- Identify the ACTUAL original descent transition of the SAME final S1
with C on the unchanged original source/window premises. Weak nonincrease
splits into strict descent or equality: the transition guard is not asserted
to accept in the equality case. No child/fold fixedness or calibration is
assumed, and no selected-leaf or final-fold equality is claimed here. -/
def ActualOriginalApplicationSidecarTransitionIdentification : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OrdinaryArithmetic.Term alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      InternalParameterizedCanonicalResultFold.sourcePremises
        (originalData data window) input typ parameter).imp
      ((InternalParameterizedBoundedDescentNormalizer.transitionGraph
          (selectedData data window).oldRepresentative
          (InternalOriginalUniformDescentSelection.validity (selectedData data window))
          out input parameter).iff
        (InternalApplicationCertificateConstructors.graph2
          (fold data window) out input parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionTargets
