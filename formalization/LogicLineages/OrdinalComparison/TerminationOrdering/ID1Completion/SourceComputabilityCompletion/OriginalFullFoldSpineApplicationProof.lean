module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalApplicationInversionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalFullFoldSpine OriginalFullFoldSpineBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof (valueUnique)
open InternalSquareRootArithmeticSupportProof (orderRight)
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Only the function-child IH is used. Both actual certified child outputs
retain their original types; the reconstructed application and final selected
leaf preserve the whole mark without any full-fold fixedness assumption. -/
theorem atRecoveredMark (base : Data) (window : Program 1)
    (q input typ out parameter mark payload arrow d e fp ap fn arg functionOut argumentOut rebuilt fm :
      OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Gamma
      (belowPayload (SpineApplicationTargets.selectedData base window) window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma
      (premises (SpineApplicationTargets.selectedData base window) window out input typ parameter)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hrecovered : Nonempty (Derivation body Gamma
      (OriginalCanonicalApplicationInversionTargets.Recovered
        (SpineApplicationTargets.selectedData base window)
        arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter)))
    (hfm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm fn))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) := by
  let data := SpineApplicationTargets.selectedData base window
  have hw := andLeft hp
  have hv := andLeft (andLeft (andRight hp))
  have hc := andLeft hrecovered
  have hcf := andLeft (andRight (andRight hrecovered))
  have hca := andLeft (andRight (andRight (andRight hrecovered)))
  have htail := andRight (andRight (andRight (andRight hrecovered)))
  have hrebuilt := andLeft htail
  have hsource := andLeft (andRight htail)
  have hleaf := andRight (andRight htail)
  have children := OriginalApplicationInverseValidityProof.sourceRecover data
    arrow d e fp ap fn arg input parameter hc hv
  have hfunctionLeft := pairLeft fn arrow fp (andLeft (andRight hc))
  have hargumentLeft := pairLeft arg d ap (andLeft (andRight (andRight hc)))
  have hfunctionSource := andIntro (andLeft (andRight children)) hfunctionLeft
  have hfunctionWindow := BottomDescentStepProof.windowChange window (suc z) input fn parameter hw
  obtain ⟨hepayload⟩ := valueUnique InternalUnpair.right payload q
    (Fin.cons input Fin.elim0) hpr hr
  obtain ⟨hfl⟩ := hfl
  have hchild := belowPayloadApply data window q fp fn arrow functionOut parameter fm hb
    ⟨orderRight fp hepayload hfl⟩ hfr
    (andIntro hfunctionWindow (andIntro hfunctionSource (andRight (andLeft hcf))))
  obtain ⟨hchildBackward⟩ := andRight hchild
  obtain ⟨hfm⟩ := hfm
  have hfunctionOutMark : Nonempty (Derivation body Gamma
      (BottomSpineMeasure.graph fm functionOut)) :=
    ⟨Derivation.implicationElimination hchildBackward hfm⟩
  have hrawInput := InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    d e fn arg fp ap input
    (pairRight fn arrow fp (andLeft (andRight hc)))
    (pairRight arg d ap (andLeft (andRight (andRight hc))))
    (andRight (andRight (andRight hc)))
  have hrebuiltIff := OriginalApplicationSidecarSpineApplicationProof.atFunctionMark
    arrow d e fn arg functionOut argumentOut input rebuilt fm mark (andLeft hc)
    hfunctionLeft hargumentLeft (andLeft (andRight (andRight hcf)))
    (andLeft (andRight (andRight hca))) hrawInput hrebuilt ⟨hfm⟩ hfunctionOutMark
  have hrebuiltWindow := BottomDescentStepProof.windowChange window (suc z)
    input rebuilt parameter hw
  have hleafIff := OriginalFullFoldSpineLeafProof.leafMarkIff base window
    out rebuilt parameter mark hrebuiltWindow (andLeft hsource) hleaf
  exact OriginalConstructorShapeApplicationProof.iffCompose
    (BottomSpineMeasure.graph mark out) (BottomSpineMeasure.graph mark rebuilt)
    (BottomSpineMeasure.graph mark input) hleafIff hrebuiltIff

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineApplicationProof
