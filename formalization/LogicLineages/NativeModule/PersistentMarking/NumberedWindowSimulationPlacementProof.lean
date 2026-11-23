module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationPlacement

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowSimulationPlacement

theorem typed {C ls rs ts} (p : Place ls rs ts) {As Bs : NArgs}
    (ha : BaseTyped C As ls) (hb : BaseTyped C Bs rs) : BaseTyped C (weave p As Bs) ts := by
  induction p generalizing As Bs with
  | nil => exact .nil
  | left rest ih =>
    cases ha with
    | cons hq htail => exact .cons hq (@ih _ _ htail hb)
  | right rest ih =>
    cases hb with
    | cons hq htail => exact .cons hq (@ih _ _ ha htail)

theorem permutation {C ls rs ts} (p : Place ls rs ts) {As Bs : NArgs}
    (ha : BaseTyped C As ls) (hb : BaseTyped C Bs rs) :
    (weave p As Bs).toList.Perm (As.toList ++ Bs.toList) := by
  induction p generalizing As Bs with
  | nil => cases ha; cases hb; exact .nil
  | left rest ih =>
    cases ha with
    | cons hq htail => exact .cons _ (@ih _ _ htail hb)
  | right rest ih =>
    cases hb with
    | cons hq htail => exact (List.Perm.cons _ (@ih _ _ ha htail)).trans List.perm_middle.symm

end LogicLineages.PersistentMarking.NumberedWindowSimulationPlacementProof
