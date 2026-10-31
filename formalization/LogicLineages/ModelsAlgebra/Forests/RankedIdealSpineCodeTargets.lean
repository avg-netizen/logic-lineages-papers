module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCodeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode.Targets
open RankedParse RankedIdealRegularCode RankedIdealCompletion RankedIdealSpine RankedGraphImage
 def FramesExact : Prop := ∀ C q c, alphabet C q c ↔ Frame C.machine q c
 def SeedsIdeal : Prop := ∀ C q rec, LowerCorrect C q rec →
   ∀ B ∈ seeds C q rec, IsIdeal (language B)
 def SeedsSound : Prop := ∀ C q rec, LowerCorrect C q rec →
   ∀ B ∈ seeds C q rec, ∀ t, language B t → Run C.machine t q
 def EntriesCovered : Prop := ∀ C q rec, LowerCorrect C q rec →
   ∀ t, Entry C.machine q t → ∃ B ∈ seeds C q rec, language B t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineCode.Targets
