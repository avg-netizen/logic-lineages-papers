module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularStateDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealRegular RankedIdealComponents RankedGraphImage

def StateLanguageExact : Prop := ∀ (M : Machine) [DecidableEq M.State] q t,
  language (stateMachine M q) t ↔ stateLanguage M q t

def CompiledNonlinearIdeal : Prop := ∀ (M : Machine) [DecidableEq M.State] q,
  NonlinearAt M q → IsIdeal (language (stateMachine M q))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularState.Targets
