module

public import LogicLineages.ModelsAlgebra.Forests.RankedParseStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.FiniteIdealCoverStatementChecks
public import LogicLineages.OrdinalComparison.WWLiteralSizeStatementChecks
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

end LogicLineages.Repair20261031Checks

#audit_namespace LogicLineages.Repair20261031Checks
