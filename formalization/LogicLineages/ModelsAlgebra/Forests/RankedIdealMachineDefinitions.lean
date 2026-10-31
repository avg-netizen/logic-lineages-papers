module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteDefinitions
public import Mathlib.Data.Fintype.Powerset
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine
open RankedParse ProfileAutomatonEncoding RankedIdealFinite
/-- Executable powerset machine for the productive downward completion.
The input equality is explicit, not obtained through classical conversion. -/
def downwardMachine (M : Machine) [DecidableEq M.State] : Machine where
  State := Finset M.State
  stateFintype := inferInstance
  leaf := close M {M.leaf}
  node := fun o S T => close M (nodeSeeds M o S T)
  accept := fun S => decide (∃ q ∈ S, M.accept q = true)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealMachine
