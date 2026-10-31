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
public import LogicLineages.OrdinalComparison.WWAdmissibleSumStatementChecks
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationGeneralStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.FiniteProfileStatementChecks
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

theorem actualAdmissibleSumSyntax : OrdinalComparison.Source.Targets.ActualAdmissibleSumSyntax :=
  OrdinalComparison.StatementChecks.fixed_actualAdmissibleSumSyntax

theorem actualAdmissibleSumValue : OrdinalComparison.Source.Targets.ActualAdmissibleSumValue :=
  OrdinalComparison.StatementChecks.fixed_actualAdmissibleSumValue

theorem actualAdmissiblePartialGenerated : OrdinalComparison.Source.Targets.ActualAdmissiblePartialGenerated :=
  OrdinalComparison.StatementChecks.fixed_actualAdmissiblePartialGenerated

theorem actualAdmissiblePartialValue : OrdinalComparison.Source.Targets.ActualAdmissiblePartialValue :=
  OrdinalComparison.StatementChecks.fixed_actualAdmissiblePartialValue

theorem forestForestRankedRepresentation : ModelsAlgebra.Forests.ForestParseRepresentation.Targets.ForestRankedRepresentation :=
  ModelsAlgebra.Forests.ForestParseRepresentation.StatementChecks.forestRankedRepresentation

theorem forestActualForbiddenLanguageImage : ModelsAlgebra.Forests.ForestParseRepresentation.Targets.ActualForbiddenLanguageImage :=
  ModelsAlgebra.Forests.ForestParseRepresentation.StatementChecks.actualForbiddenLanguageImage

theorem forestActualForbiddenIdealCover : ModelsAlgebra.Forests.ForestParseRepresentation.Targets.ActualForbiddenIdealCover :=
  ModelsAlgebra.Forests.ForestParseRepresentation.StatementChecks.actualForbiddenIdealCover

theorem generalGeneralForbiddenLanguageImage : ModelsAlgebra.Forests.ForestParseRepresentation.GeneralTargets.GeneralForbiddenLanguageImage :=
  ModelsAlgebra.Forests.ForestParseRepresentation.GeneralStatementChecks.generalForbiddenLanguageImage

theorem generalGeneralForbiddenIdealCover : ModelsAlgebra.Forests.ForestParseRepresentation.GeneralTargets.GeneralForbiddenIdealCover :=
  ModelsAlgebra.Forests.ForestParseRepresentation.GeneralStatementChecks.generalForbiddenIdealCover

theorem profileLeafExact : ModelsAlgebra.Forests.FiniteProfile.Targets.LeafExact :=
  ModelsAlgebra.Forests.FiniteProfile.StatementChecks.leafExact

theorem profileSplitEmbedding : ModelsAlgebra.Forests.FiniteProfile.Targets.SplitEmbedding :=
  ModelsAlgebra.Forests.FiniteProfile.StatementChecks.splitEmbedding

theorem profileRunExact : ModelsAlgebra.Forests.FiniteProfile.Targets.RunExact :=
  ModelsAlgebra.Forests.FiniteProfile.StatementChecks.runExact

theorem profileAcceptanceExact : ModelsAlgebra.Forests.FiniteProfile.Targets.AcceptanceExact :=
  ModelsAlgebra.Forests.FiniteProfile.StatementChecks.acceptanceExact

theorem profileAvoidanceDownward : ModelsAlgebra.Forests.FiniteProfile.Targets.AvoidanceDownward :=
  ModelsAlgebra.Forests.FiniteProfile.StatementChecks.avoidanceDownward

end LogicLineages.Repair20261031Checks

#audit_namespace LogicLineages.Repair20261031Checks
