module
public import LogicLineages.OrdinalComparison.WWFixedShiftTargets
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GeneralOmegaHeadLimit
/-- The original natural product used by actual source collapse, not ordinary
ordinal multiplication and not a polynomial-only substitute. -/
noncomputable def omegaHead (a : Ordinal.{0}) : Ordinal := ordinalNaturalProduct Ordinal.omega0 a
end LogicLineages.OrdinalComparison.Source.GeneralOmegaHeadLimit
