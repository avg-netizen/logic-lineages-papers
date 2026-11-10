module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarSpine OriginalApplicationSidecarSpineSyntaxProof
open OriginalApplicationSidecarSpineBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalSquareRootArithmeticSupportProof (orderRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Apply only the function-child observer IH. Rebuilt child type graphs come
from the already proved C invariant, never from assumed mark or fixedness laws. -/
theorem atMark (data : Data) (window : Program 1)
    (q input typ parameter payload arrow d e fp ap fn arg functionOut argumentOut out value fm : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hf : Nonempty (Derivation body Gamma (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (fold data window) argumentOut arg parameter)))
    (hfm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm fn))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  have hw := andLeft hp
  have hv := andLeft (andLeft (andRight hp))
  have hout := andRight (andRight hp)
  have children := OriginalApplicationInverseValidityProof.sourceRecover (originalData data window)
    arrow d e fp ap fn arg input parameter hc hv
  have oldFunctionLeft := pairLeft fn arrow fp (andLeft (andRight hc))
  have oldArgumentLeft := pairLeft arg d ap (andLeft (andRight (andRight hc)))
  have functionSource := andIntro (andLeft (andRight children)) oldFunctionLeft
  have argumentSource := andIntro (andRight (andRight children)) oldArgumentLeft
  have functionWindow := OriginalApplicationSidecarWindowProof.windowTransfer window (suc z) input fn parameter hw
  obtain ⟨hep⟩ := valueUnique InternalUnpair.right payload q (Fin.cons input Fin.elim0) hpr hr
  obtain ⟨hfl⟩ := hfl
  have hiff := belowPayloadApply data window q fp fn arrow functionOut parameter fm hb
    ⟨orderRight fp hep hfl⟩ hfr (andIntro functionWindow (andIntro functionSource hf))
  obtain ⟨backward⟩ := andRight hiff
  obtain ⟨hfm'⟩ := hfm
  have newFunctionMark : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm functionOut)) :=
    ⟨Derivation.implicationElimination backward hfm'⟩
  have functionInvariant := OriginalApplicationSidecarInvariantProof.invariantAtInput data window
    functionOut fn arrow parameter (andIntro functionSource hf)
  have argumentInvariant := OriginalApplicationSidecarInvariantProof.invariantAtInput data window
    argumentOut arg d parameter (andIntro argumentSource ha)
  have rawOut := OriginalApplicationSidecarEquationSupportProof.applicationBackward data window
    arrow d e fp ap fn arg input functionOut argumentOut out parameter hc hv hf ha hout
  have rawInput := InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    d e fn arg fp ap input (pairRight fn arrow fp (andLeft (andRight hc)))
    (pairRight arg d ap (andLeft (andRight (andRight hc)))) (andRight (andRight (andRight hc)))
  exact OriginalApplicationSidecarSpineApplicationProof.atFunctionMark
    arrow d e fn arg functionOut argumentOut input out fm value (andLeft hc)
    oldFunctionLeft oldArgumentLeft (andLeft (andRight functionInvariant))
    (andLeft (andRight argumentInvariant)) rawInput rawOut ⟨hfm'⟩ newFunctionMark

/-- The full function mark is an actual internally queried Program output. -/
theorem atOutputs (data : Data) (window : Program 1)
    (q input typ parameter payload arrow d e fp ap fn arg functionOut argumentOut out value : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hf : Nonempty (Derivation body Gamma (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (fold data window) argumentOut arg parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  apply programCases BottomSpineMeasure.measure (Fin.cons fn Fin.elim0) _
  intro β j Delta fm hj hfm
  rw [conclusionRename]
  simp only [consTermRename,emptyRename] at hfm
  have hb' := renameInto hb j Delta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hj
  have hpr' := renameInto hpr j Delta hj
  have hfr' := renameInto hfr j Delta hj
  rw [graph1Rename] at hr' hpr' hfr'
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hfl' := renameInto hfl j Delta hj
  unfold InternalLessThan.strictLess at hfl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl'
  have hf' := renameInto hf j Delta hj
  have ha' := renameInto ha j Delta hj
  rw [graph2Rename] at hf' ha'
  exact atMark data window (q.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) (payload.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) (out.relabel j) (value.relabel j) fm
    hb' hr' hp' hc' hpr' hfr' hfl' hf' ha' hfm

/-- Actual child C outputs are queried at the one original parameter. -/
theorem withOutputs (data : Data) (window : Program 1)
    (q input typ out parameter value payload arrow d e fp ap fn arg : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg input)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  apply OriginalApplicationSidecarInvariantQueryProof.binaryPairOutputCases (fold data window) fn arg parameter _
  intro β j Delta functionOut argumentOut hj hf ha
  rw [conclusionRename]
  have hb' := renameInto hb j Delta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hj
  have hpr' := renameInto hpr j Delta hj
  have hfr' := renameInto hfr j Delta hj
  rw [graph1Rename] at hr' hpr' hfr'
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hfl' := renameInto hfl j Delta hj
  unfold InternalLessThan.strictLess at hfl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl'
  exact atOutputs data window (q.relabel j) (input.relabel j) (typ.relabel j)
    (parameter.relabel j) (payload.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) functionOut argumentOut
    (out.relabel j) (value.relabel j) hb' hr' hp' hc' hpr' hfr' hfl' hf ha

/-- Use the original strict function-payload bound, never a whole-code bound. -/
theorem acceptedAtOutput (data : Data) (window : Program 1)
    (q input typ out parameter value : OrdinaryArithmetic.Term α)
    (hb : Nonempty (Derivation body Gamma (belowPayload data window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window)) input parameter _ hg
  intro β j Delta payload arrow d e fp ap fn arg hj hc hpr hfr _ hfl _ _
  rw [conclusionRename]
  have hb' := renameInto hb j Delta hj
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hj
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  exact withOutputs data window (q.relabel j) (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j) (value.relabel j) payload arrow d e fp ap fn arg
    hb' hr' hp' hc hpr hfr hfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineOpeningProof
