module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrderDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder.Targets
 def StateOrderExact : Prop := ∀ C x y,
   (stateOrder C).le x y ↔ C.states.idxOf x ≤ C.states.idxOf y
 def InclusionExact : Prop := ∀ C D,
   inclusion C D = true ↔ ∀ T, Represents C T → Represents D T
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrder.Targets
