module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealComponentsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealFinite RankedGraphImage

def ReachLanguageInclusion : Prop := ∀ (M : Machine) [DecidableEq M.State] x y,
  y ∈ close M {x} → ∀ t, stateLanguage M x t → stateLanguage M y t

def ComponentLanguageEquality : Prop := ∀ (M : Machine) [DecidableEq M.State] x y,
  SameComponent M x y → ∀ t, stateLanguage M x t ↔ stateLanguage M y t

def StateLanguageDownward : Prop := ∀ (M : Machine) [DecidableEq M.State] q s t,
  Homeomorphic s t → stateLanguage M q t → stateLanguage M q s

def NonlinearIdeal : Prop := ∀ (M : Machine) [DecidableEq M.State] q,
  NonlinearAt M q → IsIdeal (stateLanguage M q)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealComponents.Targets
