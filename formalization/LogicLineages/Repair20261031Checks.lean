module

public import LogicLineages.ModelsAlgebra.Forests.RankedParseStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.FiniteIdealCoverStatementChecks
public import LogicLineages.OrdinalComparison.WWLiteralSizeStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageStatementChecks
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentStatementChecks
public import LogicLineages.OrdinalComparison.WWPolicyGeneratedStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedImageCoverCompletionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithmStatementChecks
public import LogicLineages.OrdinalComparison.WWPolicyValueStatementChecks
public meta import LogicLineages.Audit

/-! Focused aggregate for the repaired-source continuation. This does not
replace, or certify a fresh build of, the full historical project root. -/

@[expose] public section
namespace LogicLineages.Repair20261031Checks

theorem homeomorphicInduced :
    ModelsAlgebra.Forests.RankedParse.Targets.HomeomorphicInduced :=
  ModelsAlgebra.Forests.RankedParse.StatementChecks.homeomorphicInduced

theorem exactPruning : ModelsAlgebra.Forests.RankedParse.Targets.ExactPruning :=
  ModelsAlgebra.Forests.RankedParse.StatementChecks.exactPruning

theorem finiteCoverCriterion : ModelsAlgebra.Forests.FiniteIdealCover.Targets.FiniteCoverCriterion :=
  ModelsAlgebra.Forests.FiniteIdealCover.StatementChecks.finiteCoverCriterion

theorem literalPartialSizeBound : OrdinalComparison.Source.Targets.ActualLiteralPartialSizeBound :=
  OrdinalComparison.StatementChecks.fixed_actualLiteralPartialSizeBound

theorem literalMultiplierBound : OrdinalComparison.Source.Targets.ActualLiteralMultiplierBound :=
  OrdinalComparison.StatementChecks.fixed_actualLiteralMultiplierBound

theorem pruneGraphEmbedding : ModelsAlgebra.Forests.RankedGraphImage.Targets.PruneGraphEmbedding :=
  ModelsAlgebra.Forests.RankedGraphImage.StatementChecks.pruneGraphEmbedding

theorem idealImage : ModelsAlgebra.Forests.RankedGraphImage.Targets.IdealImage :=
  ModelsAlgebra.Forests.RankedGraphImage.StatementChecks.idealImage

theorem imageCoverFromLanguage : ModelsAlgebra.Forests.RankedGraphImage.Targets.ImageCoverFromLanguage :=
  ModelsAlgebra.Forests.RankedGraphImage.StatementChecks.imageCoverFromLanguage

theorem imageCover : ModelsAlgebra.Forests.RankedGraphImage.Targets.ImageCover :=
  ModelsAlgebra.Forests.RankedGraphImage.StatementChecks.imageCover

theorem leftPolicyCalibration : OrdinalComparison.Source.Targets.ActualLeftPolicyPartialCalibration :=
  OrdinalComparison.StatementChecks.fixed_actualLeftPolicyPartialCalibration

theorem closedSourcePolicySeparation : OrdinalComparison.Source.Targets.ActualClosedSourcePolicySeparation :=
  OrdinalComparison.StatementChecks.fixed_actualClosedSourcePolicySeparation

theorem policyGeneratedPartial : OrdinalComparison.Source.Targets.ActualPolicyGeneratedPartial :=
  OrdinalComparison.StatementChecks.fixed_actualPolicyGeneratedPartial

theorem policyGeneratedAbstraction : OrdinalComparison.Source.Targets.ActualPolicyGeneratedAbstraction :=
  OrdinalComparison.StatementChecks.fixed_actualPolicyGeneratedAbstraction

theorem policyGeneratedAssignment : OrdinalComparison.Source.Targets.ActualPolicyGeneratedAssignment :=
  OrdinalComparison.StatementChecks.fixed_actualPolicyGeneratedAssignment

theorem policyGroundPositiveClosed : OrdinalComparison.Source.Targets.ActualPolicyGroundPositiveClosed :=
  OrdinalComparison.StatementChecks.fixed_actualPolicyGroundPositiveClosed

theorem imageCoverFromIdeals : ModelsAlgebra.Forests.RankedGraphImage.CompletionTargets.ImageCoverFromIdeals :=
  ModelsAlgebra.Forests.RankedGraphImage.CompletionStatementChecks.imageCoverFromIdeals

theorem pruningNoneExact : ModelsAlgebra.Forests.RankedPruneAlgorithm.Targets.NoneExact :=
  ModelsAlgebra.Forests.RankedPruneAlgorithm.StatementChecks.noneExact

theorem pruningSomeExact : ModelsAlgebra.Forests.RankedPruneAlgorithm.Targets.SomeExact :=
  ModelsAlgebra.Forests.RankedPruneAlgorithm.StatementChecks.someExact

theorem policyFixedInputValue : OrdinalComparison.Source.Targets.ActualPolicyFixedInputValue :=
  OrdinalComparison.StatementChecks.fixed_actualPolicyFixedInputValue

end LogicLineages.Repair20261031Checks

#audit_namespace LogicLineages.Repair20261031Checks
