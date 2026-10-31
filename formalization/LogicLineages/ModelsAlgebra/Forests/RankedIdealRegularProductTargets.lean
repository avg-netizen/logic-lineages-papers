module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProductDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealRegular RankedIdealConstructors

def ProductExact : Prop := ∀ o M N t,
  language (productMachine o M N) t ↔ ∃ l r, t = .node o l r ∧ language M l ∧ language N r

def DownwardProductExact : Prop := ∀ o (M N : Machine)
    [DecidableEq M.State] [DecidableEq N.State] t,
  language (downwardProduct o M N) t ↔ product o (language M) (language N) t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct.Targets
