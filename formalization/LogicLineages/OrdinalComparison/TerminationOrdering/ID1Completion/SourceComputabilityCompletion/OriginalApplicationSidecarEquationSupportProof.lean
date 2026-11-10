module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationInverseValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open InternalApplicationValidityClosure (applicationConstructors)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Parent validity supplies the actual two child validities and codomain
membership; none is introduced as an additional application premise. -/
theorem rootGuardFromSource (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window))
        InternalOriginalStepGuard.one parent parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))
        InternalOriginalStepGuard.one parent parameter)) := by
  have children := OriginalApplicationInverseValidityProof.sourceRecover
    (originalData data window) arrow d e fp ap fn arg parent parameter hc hv
  exact InternalParameterizedCanonicalResultFoldOpeningProof.rootGuardValue
    (originalData data window) arrow d e fp ap fn arg parent parameter hc hv
    (andLeft (andRight children)) (andRight (andRight children)) (andLeft children)

theorem rawApplicationRecover (d e f a out parameter : OrdinaryArithmetic.Term alpha)
    (h : Nonempty (Derivation body Delta
      (programGraph InternalParameterizedCanonicalResultFold.rawApplicationAt out ![d,e,f,a,parameter]))) :
    Nonempty (Derivation body Delta (graph4 application out d e f a)) := by
  let xs : Fin 5 → OrdinaryArithmetic.Term alpha := ![d,e,f,a,parameter]
  apply compositionRecover application ![.projection 0,.projection 1,.projection 2,.projection 3]
    out xs ![d,e,f,a] h
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q)))) i

theorem applicationBackward (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window))
        InternalOriginalStepGuard.one parent parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (fold data window) argumentOut arg parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 (fold data window) out parent parameter))) :
    Nonempty (Derivation body Delta (graph4 application out d e functionOut argumentOut)) := by
  have hg := rootGuardFromSource data window arrow d e fp ap fn arg parent parameter hc hv
  have combined := InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationBackward
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))
    (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    InternalParameterizedCanonicalResultFold.rawApplicationAt
    arrow d e fp ap fn arg parent functionOut argumentOut out parameter hc hg hf ha hp
  exact rawApplicationRecover d e functionOut argumentOut out parameter combined

theorem applicationForward (data : Data) (window : Program 1)
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (applicationConstructors arrow d e fp ap fn arg parent)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window))
        InternalOriginalStepGuard.one parent parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 (fold data window) functionOut fn parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (fold data window) argumentOut arg parameter)))
    (hp : Nonempty (Derivation body Delta (graph4 application out d e functionOut argumentOut))) :
    Nonempty (Derivation body Delta (graph2 (fold data window) out parent parameter)) := by
  have hg := rootGuardFromSource data window arrow d e fp ap fn arg parent parameter hc hv
  have combined := InternalParameterizedCanonicalResultFoldOpeningProof.rawApplicationValue
    d e functionOut argumentOut out parameter hp
  exact InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationForward
    (InternalParameterizedCanonicalResultFold.rootGuard (originalData data window))
    (InternalParameterizedCanonicalResultFold.leaf (originalData data window))
    InternalParameterizedCanonicalResultFold.rawApplicationAt
    arrow d e fp ap fn arg parent functionOut argumentOut out parameter hc hg hf ha combined

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
