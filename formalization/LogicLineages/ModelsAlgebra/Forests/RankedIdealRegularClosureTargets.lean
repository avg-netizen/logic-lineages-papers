module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosureDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealRegular RankedIdealConstructors RankedGraphImage

def DownwardStarExact : Prop := ∀ (M : Machine) n (rules : Fin n → Rule)
    [DecidableEq M.State] [∀ i, DecidableEq (rules i).side.State] t,
  language (downwardStar M rules) t ↔ linearPiece (allowed rules) (language M) t

def CompiledLinearIdeal : Prop := ∀ (M : Machine) n (rules : Fin n → Rule)
    [DecidableEq M.State] [∀ i, DecidableEq (rules i).side.State],
  IsIdeal (language M) → IsIdeal (language (downwardStar M rules))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure.Targets
