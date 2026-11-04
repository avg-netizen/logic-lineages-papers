module
public import LogicLineages.OrdinalComparison.ParametricFinitePairCollapseDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument
/-- The unchanged actual natural-operation argument of source collapse. -/
noncomputable def argument (a b : Nat) : Ordinal.{0} :=
  ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 (a : Ordinal)) (b : Ordinal)
end LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument
