module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Natural codes of actual decreasing-ordinal nodes respect every parent;
no finite-branching or finite ordinal-height assumption is imposed. -/
def walkerOrdinalCoding : Prop :=
  ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    Function.Injective (walkerOrdinalCode ξ) ∧
    walkerOrdinalCode ξ (walkerOrdinalRoot ξ) = 0 ∧
    ∀ s t : WalkerOrdinalNode ξ, walkerOrdinalParent ξ s = some t →
      walkerOrdinalCode ξ t < walkerOrdinalCode ξ s

/-- Every smaller ordinal occurs as the last entry of a child, exactly as in
the source defining presentation, including arbitrary infinite branching. -/
def walkerOrdinalChildren : Prop :=
  ∀ ξ : Ordinal.{0}, ∀ s : WalkerOrdinalNode ξ, ∀ β : Ordinal.{0},
    β < walkerOrdinalHeight ξ s →
      ∃ t : WalkerOrdinalNode ξ, walkerOrdinalParent ξ t = some s ∧ walkerOrdinalHeight ξ t = β

def walkerOrdinalParentHeight : Prop :=
  ∀ ξ : Ordinal.{0}, ∀ s t : WalkerOrdinalNode ξ,
    walkerOrdinalParent ξ s = some t → walkerOrdinalHeight ξ s < walkerOrdinalHeight ξ t

end LogicLineages.ModelsAlgebra.PGroups.Targets
