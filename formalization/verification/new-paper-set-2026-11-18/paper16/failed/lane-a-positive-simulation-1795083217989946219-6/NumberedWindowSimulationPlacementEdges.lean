import LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementEdges
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowPrimary
open NumberedWindowSimulationPlacement

theorem rawLeft {S K C ls rs ts} (p : Place ls rs ts) {As At Bs : NArgs}
    (hA : BaseTyped C As ls) (hT : BaseTyped C At ls) (hB : BaseTyped C Bs rs)
    (h : RawArgsStep S K As At) : RawArgsStep S K (weave p As Bs) (weave p At Bs) := by
  induction p generalizing As At Bs with
  | nil =>
    cases hA with
    | nil => cases h
  | left tail ih =>
    cases h with
    | first hs => exact .first hs
    | later hs =>
      cases hA with
      | cons _ hA' =>
        cases hT with
        | cons _ hT' => exact .later (@ih _ _ _ hA' hT' hB hs)
  | right tail ih =>
    cases hB with
    | cons _ hB' => exact .later (@ih _ _ _ hA hT hB' h)

theorem rawRight {S K C ls rs ts} (p : Place ls rs ts) {As Bs Bt : NArgs}
    (hA : BaseTyped C As ls) (hB : BaseTyped C Bs rs) (hT : BaseTyped C Bt rs)
    (h : RawArgsStep S K Bs Bt) : RawArgsStep S K (weave p As Bs) (weave p As Bt) := by
  simpa only [weaveSwap] using rawLeft (swap p) hB hT hA h

theorem eqLeft {S K C ls rs ts} (p : Place ls rs ts) {As At Bs : NArgs}
    (hB : BaseTyped C Bs rs) (h : OrderedPrimary S K C ls As At) :
    OrderedPrimary S K C ts (weave p As Bs) (weave p At Bs) := by
  induction p generalizing As At Bs with
  | nil => exact .nil
  | left tail ih =>
    cases h with
    | cons hq hs => exact .cons hq (@ih _ _ _ hB hs)
  | right tail ih =>
    cases hB with
    | cons hq hB' => exact .cons (.refl hq) (@ih _ _ _ hB' h)

theorem eqRight {S K C ls rs ts} (p : Place ls rs ts) {As Bs Bt : NArgs}
    (hA : BaseTyped C As ls) (h : OrderedPrimary S K C rs Bs Bt) :
    OrderedPrimary S K C ts (weave p As Bs) (weave p As Bt) := by
  simpa only [weaveSwap] using eqLeft (swap p) hA h

end LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementEdges
