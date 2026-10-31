module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegular.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealConstructors

def RunCalibration : Prop := ∀ (M : Machine) n (rules : Fin n → Rule) t,
  machineRun (starMachine M rules) t =
    (machineRun M t, (fun i => machineRun (rules i).side t), flag M rules t)

def StarExact : Prop := ∀ (M : Machine) n (rules : Fin n → Rule) t,
  language (starMachine M rules) t ↔ Star (allowed rules) (language M) t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegular.Targets
