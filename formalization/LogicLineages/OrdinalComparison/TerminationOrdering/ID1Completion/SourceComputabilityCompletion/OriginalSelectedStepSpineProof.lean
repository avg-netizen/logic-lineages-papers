module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationCheckerConstructorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open OriginalSpineGuardLeaf OriginalSelectedStepSpine
open OriginalSpineGuardLeafInternalProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalRefinedSelectedStepSpineGuard :
    OriginalSelectedStepSpineTargets.ActualOriginalRefinedSelectedStepSpineGuard := by
  intro endpoint oldStep
  exact OriginalSelectedStepSpineCheckerProof.actualOriginalSelectedStepSpineTransport
    endpoint (OriginalSpineGuardLeaf.refined oldStep) (leafHasSpineGuard oldStep)

/-- Every existing finalInputs leaf wrapper retains the old leaf as its
literal first conjunction factor. All selector/base refinements stay intact. -/
theorem finalLeafHasSpineGuard (p : GlobalSourcePackage.Inputs)
    (hp : LeafHasSpineGuard p.oldStep) :
    LeafHasSpineGuard (OriginalApplicationSidecar.finalInputs p).oldStep := by
  let u := OriginalConstructorShape.refineInputs
    (OriginalFunctionNeutrality.refineInputs (OriginalApplicationSidecar.refineInputs p))
  change LeafHasSpineGuard (OriginalConstructorLeaf.refined
    (OriginalNeutralLeaf.refined (OriginalNeutralLeaf.endpoint u) u.window p.oldStep))
  unfold OriginalConstructorLeaf.refined OriginalNeutralLeaf.refined
  exact conjunctionPreserves _ _ (conjunctionPreserves _ _ hp)

/-- Recover the literal selected-checker factor from complete guarded
raw-step acceptance, and use the internally paid leaf law. -/
theorem rawStepHasSpineGuard (data : Data) (leaf : Program 4)
    (hLeaf : LeafHasSpineGuard leaf) : RawStepHasSpineGuard data leaf := by
  intro body alpha Delta s t k parameter
  let P := UniformCertificateCompletion.stepAccepted data leaf s t k parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := OriginalNonapplicationCheckerConstructorProof.selectedAcceptance
    data leaf s t k parameter hp
  obtain ⟨h⟩ := OriginalSelectedStepSpineCheckerProof.checkerValue
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint data)
    leaf hLeaf s t k parameter hs
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalFinalRawStepSpineGuard :
    OriginalSelectedStepSpineTargets.ActualOriginalFinalRawStepSpineGuard := by
  intro p
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  exact rawStepHasSpineGuard (OuterSelection.data r.base r.window) r.oldStep
    (finalLeafHasSpineGuard q (leafHasSpineGuard p.oldStep))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineProof
