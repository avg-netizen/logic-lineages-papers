module

public import LogicLineages.NativeModule.PersistentMarking.RefinementOpeningProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementFreshOpeningProof
open Spine NameBridge

theorem opening : RefinementSyntaxTargets.Opening := by
  intro S σ q s x h hxq hxs
  obtain ⟨h⟩ := h
  cases h with
  | @abs _ _ _ _ y _ _ hyq hys body =>
    obtain ⟨out,_⟩ := RefinementOpeningProof.synchronize S σ y x q s hyq hys hxq hxs body
    exact ⟨out⟩
end LogicLineages.PersistentMarking.RefinementFreshOpeningProof
