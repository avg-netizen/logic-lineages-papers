module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilitySoundnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelCollisionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionProof
open UniformCertificateCompletion SixSol20261113.Context
open SixSol20261113.Erasure
open EvaluatorFibreCountermodel
open RetainedCompatibilityObstruction RetainedCompatibilitySoundnessProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualRetainedFields : RetainedCompatibilityObstructionTargets.ActualRetainedFields := by
  intro p H G W
  exact ⟨rfl,rfl⟩

theorem actualProjectionObstruction : RetainedCompatibilityObstructionTargets.ActualProjectionObstruction := by
  have hw := EvaluatorFibreCountermodelWindowProof.actualWindow
  obtain ⟨q,hq⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection 1 arity
  obtain ⟨H,hH⟩ := OriginalTypedDecoderHeadSelectionProof.actualOriginalTypedHeadSelection 1 arity
  obtain ⟨G,hG⟩ := OriginalVariableLeavesContextGuardProof.actualOriginalVariableContextGuardSelection 1
  obtain ⟨W,hW⟩ := OriginalUniverseDecoderWindowSelectionProof.actualOriginalUniverseWindowSelection 1 arity
  let M := InternalOriginalUniformContextMembership.contextMember q.base.member
  have hM : OriginalUniverseDecoder.ContextMemberCalibrated 1 M :=
    OriginalUniverseDecoderGuardCalibrationProof.originalMemberCalibration 1 q.base.member hq.1.2.2.2
  have hl := EvaluatorFibreCountermodelSourceProof.sourceAt H G M W hH hG hM hW
    leftTerm hw.2.2.2.2.1
  have hr := EvaluatorFibreCountermodelSourceProof.sourceAt H G M W hH hG hM hW
    rightTerm hw.2.2.2.2.2
  have hR : EvaluatorKeyPut.baseRepresentative (projectionInputs q) H G W = representative := rfl
  have hmember : EvaluatorKeyPut.member (projectionInputs q) H G W = M := rfl
  have hE : EvaluatorKeyPut.evaluatorKey (projectionInputs q) H G W = evaluator := rfl
  refine ⟨hw,q,H,G,W,hq,hH,hG,hW,?_,?_,?_,?_,?_⟩
  · rw [hmember]
    exact hl
  · rw [hmember]
    exact hr
  · rw [hE]
    exact EvaluatorFibreCountermodelCollisionProof.evaluatorEqual
  · rw [hR]
    exact EvaluatorFibreCountermodelCollisionProof.representativeDifferent
  · change ¬ EvaluatorConstructorCongruenceDefinitions.UniformRetainedCompatibility
      (EvaluatorKeyPut.baseRepresentative (projectionInputs q) H G W) H G
        (EvaluatorKeyPut.member (projectionInputs q) H G W) W
    rw [hR,hmember]
    exact incompatibleOfCollision representative H G M W leftCode rightCode parameter hl hr
      EvaluatorFibreCountermodelCollisionProof.evaluatorEqual
      EvaluatorFibreCountermodelCollisionProof.representativeDifferent
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionProof
