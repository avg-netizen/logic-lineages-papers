module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState
open RankedParse ProfileAutomatonEncoding RankedIdealFinite

def stateMachine (M : Machine) [DecidableEq M.State] (q : M.State) : Machine where
  State := Finset M.State
  stateFintype := inferInstance
  leaf := close M {M.leaf}
  node := fun o S T => close M (nodeSeeds M o S T)
  accept := fun S => decide (q ∈ S)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState
