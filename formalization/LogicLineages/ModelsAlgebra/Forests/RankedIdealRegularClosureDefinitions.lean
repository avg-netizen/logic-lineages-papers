module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure
open RankedParse ProfileAutomatonEncoding RankedIdealRegular

def downwardStar (M : Machine) {n} (rules : Fin n → Rule)
    [DecidableEq M.State] [∀ i, DecidableEq (rules i).side.State] : Machine :=
  letI : DecidableEq (starMachine M rules).State :=
    inferInstanceAs (DecidableEq (M.State × ((i : Fin n) → (rules i).side.State) × Bool))
  RankedIdealMachine.downwardMachine (starMachine M rules)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure
