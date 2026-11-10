module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityRootTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalApplicationValidityClosure (applicationConstructors)
open InternalApplicationCertificateConstructorsSupportProof (pairLeft pairRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSupportProof (refl)

/-- Actual child C outputs share the original function tag. The original
lambda/nonlambda equations then give the same parent neutrality value. -/
theorem atOutputs (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg input functionOut argumentOut out parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hcon : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (fold data window) argumentOut arg parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalFunctionNeutrality.markGraph value out).iff (OriginalFunctionNeutrality.markGraph value input))) := by
  have happ := OriginalApplicationSidecarEquationSupportProof.applicationBackward data window
    arrow d e fp ap fn arg input functionOut argumentOut out parameter hcon hv hf ha hc
  have children := OriginalApplicationInverseValidityProof.sourceRecover (originalData data window)
    arrow d e fp ap fn arg input parameter hcon hv
  have hfnSource : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) fn arrow parameter)) :=
    andIntro (andLeft (andRight children)) (pairLeft fn arrow fp (andLeft (andRight hcon)))
  have hfnWindow := OriginalApplicationSidecarWindowProof.windowTransfer
    window (suc z) input fn parameter hw
  have originalRaw := InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    d e fn arg fp ap input (pairRight fn arrow fp (andLeft (andRight hcon)))
    (pairRight arg d ap (andLeft (andRight (andRight hcon)))) (andRight (andRight (andRight hcon)))
  apply programCases OriginalConstructorShape.tag (Fin.cons fn Fin.elim0) _
  intro beta j Theta tag hj ht
  rw [OriginalFunctionNeutralityGuardProof.markIffRename]
  simp only [consTermRename,emptyRename] at ht
  have htag : Nonempty (Derivation body Theta
      (OriginalConstructorShape.tagGraph tag (fn.relabel j))) := ht
  have hw' := renameInto hfnWindow j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hw'
  have hs' := renameInto hfnSource j Theta hj
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename] at hs'
  have hf' := renameInto hf j Theta hj
  rw [graph2Rename] at hf'
  have houtputTag := OriginalApplicationSidecarNeutralityRootTagProof.tagTransport data window
    (functionOut.relabel j) (fn.relabel j) (arrow.relabel j) (parameter.relabel j) tag
    hw' hs' hf' htag
  have hi' := renameInto originalRaw j Theta hj
  have ho' := renameInto happ j Theta hj
  rw [graph4Rename] at hi' ho'
  apply formulaCases (eqn tag (suc z))
  · let A := eqn tag (suc z)
    have he : Nonempty (Derivation body (A :: Theta) A) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BottomRepresentativeInternalProof.indicatorIff OriginalNeutralLeaf.neutralTest
      (value.relabel j) (out.relabel j) (input.relabel j) z z
      (OriginalFunctionNeutralityApplicationValuesProof.neutralAtLambda
        (d.relabel j) (e.relabel j) (functionOut.relabel j) (argumentOut.relabel j)
        (out.relabel j) tag (withHyp ho' A) (withHyp houtputTag A) he)
      (OriginalFunctionNeutralityApplicationValuesProof.neutralAtLambda
        (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
        (input.relabel j) tag (withHyp hi' A) (withHyp htag A) he) ⟨refl z⟩
  · let A := (eqn tag (suc z)).not
    have he : Nonempty (Derivation body (A :: Theta) A) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BottomRepresentativeInternalProof.indicatorIff OriginalNeutralLeaf.neutralTest
      (value.relabel j) (out.relabel j) (input.relabel j) (suc z) (suc z)
      (OriginalFunctionNeutralityApplicationValuesProof.neutralAtNonlambda
        (d.relabel j) (e.relabel j) (functionOut.relabel j) (argumentOut.relabel j)
        (out.relabel j) tag (withHyp ho' A) (withHyp houtputTag A) he)
      (OriginalFunctionNeutralityApplicationValuesProof.neutralAtNonlambda
        (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
        (input.relabel j) tag (withHyp hi' A) (withHyp htag A) he) ⟨refl (suc z)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationValuesProof
