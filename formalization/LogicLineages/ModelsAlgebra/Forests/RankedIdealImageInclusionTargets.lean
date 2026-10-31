module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCodeOrderDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealImageInclusion.Targets
open RankedIdealRegularCode RankedGraphImage
/-- Exact source graph-image inclusion, not binary-language inclusion. -/
 def ImageInclusionExact : Prop := ∀ C D,
   RankedIdealCodeOrder.inclusion C D = true ↔
     ∀ G, Image (language C) G → Image (language D) G
end LogicLineages.ModelsAlgebra.Forests.RankedIdealImageInclusion.Targets
