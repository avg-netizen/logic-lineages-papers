module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFiniteTargets
public import LogicLineages.OrdinalComparison.SourceMachinePlanFiniteProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.StatementChecks
theorem forward_renaming : Targets.ForwardRenaming := Proof.forwardRenaming
theorem constructor_preservation : Targets.ConstructorPreservation := Proof.constructorPreservation
theorem actual_plan_uniformity : Targets.ActualPlanUniformity := Proof.actualPlanUniformity
theorem actual_gamma_forest : Targets.ActualGammaForest := Proof.actualGammaForest
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite
