module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerConstructionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- The source ordinal cut, with original multiplication order. -/
abbrev walkerGammaCut (γ : Ordinal.{0}) : Ordinal.{0} := Ordinal.omega0 * γ
end LogicLineages.ModelsAlgebra.PGroups
