module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionTargets
open UniformCertificateCompletion SixSol20261113.Context
open SixSol20261113.Erasure.EvaluatorFibreCountermodel
open RetainedCompatibilityObstruction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal retained fields at the SAME evaluator-aware tuple, before its
minimum/final pipeline. This is AST identity, not native calibration. -/
def ActualRetainedFields : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  EvaluatorKeyPut.baseRepresentative p H G W = p.base.oldRepresentative ∧
  EvaluatorKeyPut.member p H G W = InternalOriginalUniformContextMembership.contextMember p.base.member
/-- An actual original selected q with only its representative replaced by
projection. Both genuine source terms, their original finite window and paired
context/Gamma coordinates are the frozen countermodel's unchanged ones.
The actual NEW tuple's E agrees, its retained R differs, and its uniform INTERNAL
compatibility rule fails. This refutes unrestricted compatibility, not the
calibrated original representative or unconditional Object cancellation. -/
def ActualProjectionObstruction : Prop :=
  SixSol20261113.Erasure.EvaluatorFibreCountermodelTargets.ActualWindow ∧
  ∃ (q : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated 1 arity q ∧
  OriginalTypedDecoder.HeadSignatureCalibrated 1 arity H ∧
  OriginalTypedDecoder.ContextGuardCalibrated 1 G ∧
  OriginalUniverseDecoder.HeadWindowCalibrated 1 arity W ∧
  evaluate (OriginalUniverseDecoder.source H G (EvaluatorKeyPut.member (projectionInputs q) H G W) W)
    (List.Vector.ofFn ![leftCode,parameter]) = 1 ∧
  evaluate (OriginalUniverseDecoder.source H G (EvaluatorKeyPut.member (projectionInputs q) H G W) W)
    (List.Vector.ofFn ![rightCode,parameter]) = 1 ∧
  evaluate (EvaluatorKeyPut.evaluatorKey (projectionInputs q) H G W)
    (List.Vector.ofFn ![leftCode,parameter]) =
    evaluate (EvaluatorKeyPut.evaluatorKey (projectionInputs q) H G W)
      (List.Vector.ofFn ![rightCode,parameter]) ∧
  evaluate (EvaluatorKeyPut.baseRepresentative (projectionInputs q) H G W)
    (List.Vector.ofFn ![leftCode,parameter]) ≠
    evaluate (EvaluatorKeyPut.baseRepresentative (projectionInputs q) H G W)
      (List.Vector.ofFn ![rightCode,parameter]) ∧
  ¬ EvaluatorKeyCanonicalPreservationDefinitions.Compatible (projectionInputs q) H G W
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.RetainedCompatibilityObstructionTargets
