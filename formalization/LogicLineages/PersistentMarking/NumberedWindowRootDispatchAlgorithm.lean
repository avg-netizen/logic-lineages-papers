module

public import LogicLineages.PersistentMarking.NumberedWindowBinderRootAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowSelectAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowStatRootAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAddressAlgorithm (contextView)

structure Rules where
  mark : Nat → Nat → Nat → Bool
  lower : Nat → Nat → Bool
  select : Bool → Nat → List Nat → Nat → Nat → Bool
  copy : Nat → Nat → Bool
  stat : Nat → Nat → Nat → Bool
  fabs : Nat → Nat → Bool
  beta : Nat → Nat → Bool
  bottom : Nat → Nat → Bool

def fixed (entries : NumberedWindowCopyAlgorithm.Entries) (heads : List Nat) : Rules where
  mark := NumberedWindowMarkRootAlgorithm.mark
  lower := NumberedWindowMarkRootAlgorithm.lower
  select := NumberedWindowSelectAlgorithm.select
  copy := NumberedWindowCopyAlgorithm.copy entries heads
  stat := NumberedWindowStatRootAlgorithm.stat entries heads
  fabs := NumberedWindowBinderRootAlgorithm.fabs
  beta := NumberedWindowBinderRootAlgorithm.beta
  bottom := NumberedWindowMarkRootAlgorithm.bottom

def flagView : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def parts (rules : Rules) (q r : Nat) : Nat → List Nat → Bool
  | 0, [k] => rules.mark k q r
  | 1, [] => rules.lower q r
  | 2, [flag,i,dom] =>
    (flagView flag).any (fun extra =>
      (contextView dom).any (fun domains => rules.select extra i domains q r))
  | 3, [] => rules.copy q r
  | 4, [part] =>
    (NumberedWindowStatAlgorithm.readPartition part).isSome && rules.stat part q r
  | 5, [] => rules.fabs q r
  | 6, [] => rules.beta q r
  | 7, [] => rules.bottom q r
  | _, _ => false

def check (rules : Rules) (q cert r : Nat) : Bool :=
  (unpackNode cert).any (fun p => parts rules q r p.1 p.2)

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
