module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeApplicationMarkProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalApplicationValidityClosure (applicationConstructors)
open InternalApplicationCertificateConstructorsSupportProof (pairRight)
open InternalTagArithmeticSupportProof (refl)

/-- Original and rebuilt raw applications both have the actual variable mark
zero. The original helper binds fresh payloads for rebuilt children internally. -/
theorem atOutputs (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg input functionOut argumentOut out parameter value : OrdinaryArithmetic.Term alpha)
    (hcon : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (fold data window) argumentOut arg parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalVariableRepresentative.markGraph value out).iff (OriginalVariableRepresentative.markGraph value input))) := by
  have outputRaw := OriginalApplicationSidecarEquationSupportProof.applicationBackward data window
    arrow d e fp ap fn arg input functionOut argumentOut out parameter hcon hv hf ha hc
  have originalRaw := InternalApplicationCertificateConstructorsSupportProof.applicationBackward
    d e fn arg fp ap input (pairRight fn arrow fp (andLeft (andRight hcon)))
    (pairRight arg d ap (andLeft (andRight (andRight hcon)))) (andRight (andRight (andRight hcon)))
  have ho := OriginalVariableRepresentativeApplicationMarkProof.applicationMarkZero
    d e functionOut argumentOut out outputRaw
  have hi := OriginalVariableRepresentativeApplicationMarkProof.applicationMarkZero d e fn arg input originalRaw
  exact BottomRepresentativeInternalProof.indicatorIff OriginalVariableRepresentative.variableMark
    value out input z z ho hi ⟨refl z⟩

/-- Child values are internally queried at the same parameter, never supplied
as additional premises of the frozen target. No child invariant is needed. -/
theorem atConstructors (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg input out parameter value : OrdinaryArithmetic.Term alpha)
    (hcon : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg input)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalVariableRepresentative.markGraph value out).iff (OriginalVariableRepresentative.markGraph value input))) := by
  apply OriginalApplicationSidecarInvariantQueryProof.binaryPairOutputCases (fold data window) fn arg parameter _
  intro beta j Theta functionOut argumentOut hj hf ha
  rw [OriginalVariableRepresentativeGuardProof.markIffRename]
  have hcon' := renameInto hcon j Theta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hcon'
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  exact atOutputs data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (input.relabel j)
    functionOut argumentOut (out.relabel j) (parameter.relabel j) (value.relabel j)
    hcon' hv' hf ha hc'

/-- Actual guard opening supplies the original raw constructor witnesses. -/
theorem openingMarkIff (data : Data) (window : Program 1)
    (out input parameter value : OrdinaryArithmetic.Term alpha)
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (fold data window) out input parameter)))
    (hg : Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))) (suc z) input parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalVariableRepresentative.markGraph value out).iff (OriginalVariableRepresentative.markGraph value input))) := by
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window)) input parameter _ hg
  intro beta j Theta payload arrow d e fp ap fn arg hj hcon _ _ _ _ _ _
  rw [OriginalVariableRepresentativeGuardProof.markIffRename]
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hv'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  exact atConstructors data window arrow d e fp ap fn arg (input.relabel j)
    (out.relabel j) (parameter.relabel j) (value.relabel j) hcon hv' hc'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarVariableMarkApplicationProof
