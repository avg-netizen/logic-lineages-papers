module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual final canonical output is fixed by the acyclic sidecar C.
Original source and window premises suffice: transition fixedness is obtained
from the checked canonical consumer, then transferred by the actual T iff C.
No N-, leaf-, child- or C-fixedness hypothesis is supplied. -/
def ActualOriginalApplicationSidecarCanonicalOutputFixed : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter : OrdinaryArithmetic.Term alpha),
  let after := selectedData data window
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises after input typ parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph after out input parameter)).imp
      (InternalApplicationCertificateConstructors.graph2
        (fold data window) out out parameter)))

/-- The SAME actual final selected leaf has precisely the identity graph at
an application rebuilt from actual final canonical child outputs. All child
validities, types and sidecar fixedness are derived from original parent
validity and those graphs. Original payloads remain input witnesses; fresh
output payloads are bound internally. No final-leaf equality is a premise. -/
def ActualOriginalApplicationSidecarSameFinalLeaf : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (arrow d e fp ap fn arg parent functionOut argumentOut rebuilt out parameter : OrdinaryArithmetic.Term alpha),
  let after := selectedData data window
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window parent parameter ⊓
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
        (InternalApplicationCertificateConstructors.graph2
          (InternalOriginalUniformDescentSelection.validity after)
          InternalOriginalStepGuard.one parent parameter ⊓
          (InternalParameterizedCanonicalResultFold.foldGraph after functionOut fn parameter ⊓
            (InternalParameterizedCanonicalResultFold.foldGraph after argumentOut arg parameter ⊓
              InternalApplicationCertificateConstructors.graph4
                InternalApplicationCertificateConstructors.application rebuilt d e functionOut argumentOut))))).imp
      ((InternalApplicationCertificateConstructors.graph2
          (InternalParameterizedCanonicalResultFold.leaf after) out rebuilt parameter).iff
        (InternalControlGraph.equal out rebuilt))))

/-- Exact application factorization for the ACTUAL final canonical fold,
not a replacement by C. The original application and both actual canonical
child graphs determine the raw rebuilt result through the SAME final leaf.
No child success, invariant, fixedness, window-membership or calibration
hypothesis is added. -/
def ActualOriginalApplicationSidecarCanonicalApplicationEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (alpha : Type) (Delta : List (Formula alpha))
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term alpha),
  let after := selectedData data window
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph window parent parameter ⊓
      (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
        (InternalApplicationCertificateConstructors.graph2
          (InternalOriginalUniformDescentSelection.validity after)
          InternalOriginalStepGuard.one parent parameter ⊓
          (InternalParameterizedCanonicalResultFold.foldGraph after functionOut fn parameter ⊓
            InternalParameterizedCanonicalResultFold.foldGraph after argumentOut arg parameter)))).imp
      ((InternalParameterizedCanonicalResultFold.foldGraph after out parent parameter).iff
        (InternalApplicationCertificateConstructors.graph4
          InternalApplicationCertificateConstructors.application out d e functionOut argumentOut))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafTargets
