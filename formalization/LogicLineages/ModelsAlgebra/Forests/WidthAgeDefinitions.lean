module

public import LogicLineages.ModelsAlgebra.Forests.AgeDefinitions
public import LogicLineages.ModelsAlgebra.Forests.WidthJEPDefinitions

/-! Literal finite antichain-width classes for the countable-age application. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeConstruction

def WidthClass (m : Nat) (F : FiniteOrderForest) : Prop := WidthAtMost F.Carrier m

end LogicLineages.ModelsAlgebra.Forests.AgeConstruction
