module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarRootMarkApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationProof
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

/-- Child values are internally queried at the same parameter, never supplied
as additional premises of the frozen target. No child invariant is needed. -/
theorem atConstructors (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg input out parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hcon : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalFunctionNeutrality.markGraph value out).iff (OriginalFunctionNeutrality.markGraph value input))) := by
  apply OriginalApplicationSidecarInvariantQueryProof.binaryPairOutputCases (fold data window) fn arg parameter _
  intro beta j Theta functionOut argumentOut hj hf ha
  rw [OriginalFunctionNeutralityGuardProof.markIffRename]
  have hw' := renameInto hw j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have hcon' := renameInto hcon j Theta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hcon'
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  exact OriginalApplicationSidecarNeutralityApplicationValuesProof.atOutputs data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (input.relabel j)
    functionOut argumentOut (out.relabel j) (parameter.relabel j) (value.relabel j)
    hw' hcon' hv' hf ha hc'

/-- Actual guard opening supplies the original raw constructor witnesses. -/
theorem openingMarkIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hw : Nonempty (Derivation body Delta (OriginalFunctionNeutrality.windowGraph window input parameter)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (hg : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) (suc z) input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalFunctionNeutrality.markGraph value out).iff (OriginalFunctionNeutrality.markGraph value input))) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window)) input parameter _ hg
  intro beta j Theta payload arrow d e fp ap fn arg hj hcon _ _ _ _ _ _
  rw [OriginalFunctionNeutralityGuardProof.markIffRename]
  have hw' := renameInto hw j Theta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  exact atConstructors data window arrow d e fp ap fn arg (input.relabel j)
    (out.relabel j) (parameter.relabel j) (value.relabel j) hw' hcon hv' hc'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarNeutralityApplicationProof
