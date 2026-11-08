module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberCertifiedLift
open InternalOriginalObjectFiberCertifiedLiftTargets InternalOriginalObjectFiberCertifiedLiftSyntaxProof
open InternalComputabilityDownwardSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualInternalOriginalObjectFunctionFiber : ActualInternalOriginalObjectFunctionFiber :=
  InternalOriginalObjectFiberCertifiedLiftWrapperProof.actualInternalOriginalObjectFunctionFiber

theorem actualInternalOriginalObjectTargetFiber : ActualInternalOriginalObjectTargetFiber :=
  InternalOriginalObjectFiberCertifiedLiftWrapperProof.actualInternalOriginalObjectTargetFiber

theorem actualInternalOriginalObjectFiberTypedGraph : ActualInternalOriginalObjectFiberTypedGraph :=
  InternalOriginalObjectFiberCertifiedLiftWrapperProof.actualInternalOriginalObjectFiberTypedGraph

theorem actualInternalOriginalObjectFiberPositiveRecovery : ActualInternalOriginalObjectFiberPositiveRecovery :=
  InternalOriginalObjectFiberCertifiedLiftWrapperProof.actualInternalOriginalObjectFiberPositiveRecovery

theorem actualInternalOriginalObjectFiberPositiveReconstruction : ActualInternalOriginalObjectFiberPositiveReconstruction :=
  InternalOriginalObjectFiberCertifiedLiftWrapperProof.actualInternalOriginalObjectFiberPositiveReconstruction

theorem actualInternalOriginalObjectFiberInputExtraction : ActualInternalOriginalObjectFiberInputExtraction :=
  InternalOriginalObjectFiberCertifiedLiftInputProof.actualInternalOriginalObjectFiberInputExtraction

theorem actualInternalOriginalObjectFiberApplicationResult : ActualInternalOriginalObjectFiberApplicationResult :=
  InternalOriginalObjectFiberCertifiedLiftResultProof.actualInternalOriginalObjectFiberApplicationResult

theorem actualInternalOriginalObjectFiberRawTransport : ActualInternalOriginalObjectFiberRawTransport :=
  InternalOriginalObjectFiberCertifiedLiftTransportProof.actualInternalOriginalObjectFiberRawTransport

/-- Eliminate the internally obtained raw output pair and reconstruct every
original source wrapper at the SAME supplied endpoints and certificate. -/
theorem actualInternalOriginalObjectFiberSourceLift : ActualInternalOriginalObjectFiberSourceLift := by
  intro S K Gamma p hm hc hw body α Delta sigma tau f g a out other witness lifted
  let P := fiberPremises (src K Gamma p) (comp K Gamma p) (lift K Gamma p)
    K Gamma sigma tau f g a out other witness lifted
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ho := InternalOriginalObjectFiberCertifiedLiftTransportProof.rawTransport
    S K Gamma p hm hc hw sigma tau f g a out other witness lifted hp
  have result : Nonempty (Derivation body (P :: Delta)
      (InternalAccessibilityRules.certificate (src K Gamma p) false K out other lifted)) := by
    apply transportedOutputsCases Gamma p tau out other lifted _ ho
    intro β j Theta x y hj hout
    rw [certificateRename]
    exact InternalOriginalObjectFiberCertifiedLiftWrapperSupportProof.positiveAccept
      K Gamma p hw tau (out.relabel j) (other.relabel j) (lifted.relabel j) x y hout
  obtain ⟨d⟩ := result
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualInternalOriginalObjectFiberCertifiedApplicationLift :
    ActualInternalOriginalObjectFiberCertifiedApplicationLift := by
  intro S K Gamma p hm hc hw α sigma tau f g a out other witness lifted
  exact actualInternalOriginalObjectFiberSourceLift S K Gamma p hm hc hw
    (SourcePresentation.sourceBody (src K Gamma p) K) α [] sigma tau f g a out other witness lifted

/-- Keep the complete previously accepted assembly witness and append only
its proved fixed-fiber internal lift. No source/path witness is exchanged. -/
theorem actualOriginalSelectedObjectFiberCertifiedApplicationLift :
    ActualOriginalSelectedObjectFiberCertifiedApplicationLift := by
  intro n arity symbols S Gamma table hc
  obtain ⟨p,hi,hs,happ,hpatched,hassembled,hgraphs,hsource⟩ :=
    InternalOriginalObjectFiberSourceAssemblyProof.actualOriginalSelectedObjectFiberSourceAssembly
      n arity symbols S Gamma table hc
  let K := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hm : InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member := hi.1.2.1
  have hwcal : WindowCalibrated n p.window := hi.2.2.2.2.2.2
  have hw : evaluate p.window (List.Vector.ofFn ![K]) = 1 := by
    rw [hwcal]
    exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hc
  exact ⟨p,hi,hs,happ,hpatched,hassembled,hgraphs,hsource,
    actualInternalOriginalObjectFiberSourceLift S K Gamma p hm hc hw,
    actualInternalOriginalObjectFiberCertifiedApplicationLift S K Gamma p hm hc hw⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftProof
