module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComponentCoherenceGlobalInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
open UniformCertificateCompletion OriginalHereditaryLambdaGlobal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- These are literal AST identities. The neutral endpoint uses base/window
fields only, so the inner and outer effective wrappers have identical guards. -/
theorem pipelineIdentities (p : GlobalSourcePackage.Inputs) :
    (priorFinal p).oldStep = wrapper (endpoint p) p.window p.oldStep ∧
      endpoint (prepareInputs p) = endpoint p ∧
      (finalInputs p).oldStep = closedLeaf (endpoint p) p.window p.oldStep := by
  exact ⟨rfl,rfl,rfl⟩

/-- The whole inner effective leaf is calibrated using the existing spine
and final-input constructors BEFORE hereditary refinement is applied. -/
theorem priorFinalCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (priorFinal p) :=
  OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated
    n arity (OriginalSpineGuardLeaf.refineInputs p)
    (OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp)

/-- Only the prepared oldStep changes. Its inner leaf already has the exact
original all-input calibration; no internal graph law is transported here. -/
theorem prepareInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (prepareInputs p) := by
  have hi := priorFinalCalibrated n arity p hp
  obtain ⟨hbase,hwindow,hsrc,hcomp,hstep,hvertex,hresult⟩ := hp
  refine ⟨hbase,hwindow,hsrc,hcomp,?_,hvertex,hresult⟩
  intro v
  exact (OriginalHereditaryLambdaEvaluationProof.actualOriginalHereditaryLambdaRefinementEquality
    n arity (priorFinal p).oldStep hi.2.2.2.2.1 v).trans (hi.2.2.2.2.1 v)

/-- All three leaves compute the original leaf value on every raw vector.
This numerical equality remains independent of effective-leaf child closure. -/
theorem nativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    NativePreparation n arity p := by
  have hi := priorFinalCalibrated n arity p hp
  have hprepared := prepareInputsCalibrated n arity p hp
  have hfinal := priorFinalCalibrated n arity (prepareInputs p) hprepared
  refine ⟨hi,hprepared,hfinal,?_⟩
  intro v
  exact ⟨(hi.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm,
    (hprepared.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm,
    (hfinal.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm⟩

theorem actualOriginalHereditaryLambdaGlobalPreparation :
    OriginalHereditaryLambdaGlobalTargets.ActualOriginalHereditaryLambdaGlobalPreparation :=
  ⟨pipelineIdentities,nativePreparation⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
