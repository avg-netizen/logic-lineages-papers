module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealSpineDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealCompletion RankedIdealComponents RankedIdealConstructors
 def EntrySound : Prop := ∀ (M : Machine) [DecidableEq M.State] q t,
   Entry M q t → Run M t q
 def FrameSound : Prop := ∀ (M : Machine) [DecidableEq M.State] q c t,
   Frame M q c → Run M t q → Run M (RankedIdealContext.plug c t) q
 def LinearSpineExact : Prop := ∀ (M : Machine) [DecidableEq M.State] q,
   ¬NonlinearAt M q → ∀ t,
   Run M t q ↔ Star (Frame M q) (Entry M q) t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSpine.Targets
