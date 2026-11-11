module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeRefinementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
open UniformCertificateCompletion OriginalLambdaTraversalSelection

/-- All seven original global input calibration fields survive; only base
was prepared. This supplies no internal canonical/body law by reflection. -/
theorem prepareInputsCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (prepareInputs p) :=
  ⟨(OriginalLambdaTraversalNativeRefinementProof.actualOriginalLambdaTraversalRefinementEquality
    n arity p.base p.window hp.1 hp.2.1).2,hp.2⟩

theorem actualOriginalLambdaTraversalNativePreparation :
    OriginalLambdaTraversalSelectionTargets.ActualOriginalLambdaTraversalNativePreparation := by
  intro n arity p hp
  have hprepared := prepareInputsCalibrated n arity p hp
  have hfinal := OriginalHereditaryLambdaGlobalPreparationProof.nativePreparation
    n arity (prepareInputs p) hprepared
  refine ⟨hprepared,hfinal.2.2.1,?_⟩
  intro v
  have ht := (OriginalTransparentLambdaValidityRefinementProof.actualOriginalTransparentRefinementCalibration
    n arity p.base hp.1).2.2.1 v
  exact ⟨ht.1,ht.2.1,
    OriginalLambdaTraversalNativeRefinementProof.representativeUnchanged
      n arity p.base p.window hp.1 hp.2.1 v,ht.2.2.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
