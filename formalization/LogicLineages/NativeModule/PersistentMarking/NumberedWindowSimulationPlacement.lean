module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationJobs

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationPlacement
open NumberedWindowSyntax

/-- A literal target occurrence schedule. Each left/right position retains
its assigned type and ordered component, and there is no third position. -/
inductive Place : List Ty → List Ty → List Ty → Type where
  | nil : Place [] [] []
  | left : Place ls rs ts → Place (a::ls) rs (a::ts)
  | right : Place ls rs ts → Place ls (a::rs) (a::ts)

def weave {ls rs ts} (p : Place ls rs ts) (As Bs : NArgs) : NArgs :=
  match p with
  | .nil => .nil
  | .left rest =>
    match As with
    | .nil => .nil
    | .cons q qs => .cons q (weave rest qs Bs)
  | .right rest =>
    match Bs with
    | .nil => .nil
    | .cons q qs => .cons q (weave rest As qs)

def swap {ls rs ts} (p : Place ls rs ts) : Place rs ls ts :=
  match p with
  | .nil => .nil
  | .left rest => .right (swap rest)
  | .right rest => .left (swap rest)

theorem weaveSwap {ls rs ts} (p : Place ls rs ts) (As Bs : NArgs) :
    weave (swap p) Bs As = weave p As Bs := by
  induction p generalizing As Bs with
  | nil => rfl
  | left rest ih =>
    cases As with
    | nil => rfl
    | cons q qs => exact congrArg (NArgs.cons q) (ih qs Bs)
  | right rest ih =>
    cases Bs with
    | nil => rfl
    | cons q qs => exact congrArg (NArgs.cons q) (ih As qs)

end LogicLineages.PersistentMarking.NumberedWindowSimulationPlacement
