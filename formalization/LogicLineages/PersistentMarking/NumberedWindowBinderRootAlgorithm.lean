module
public import LogicLineages.PersistentMarking.NumberedWindowSingletonAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowBinderRootAlgorithm
open NumberedWindowFieldAlgorithm (pack packNode unpack unpackNode)
open NumberedWindowMarkRootAlgorithm (guarded)

def freshBody (f dom cod label base extras : Nat) : Option Nat := do
  let shiftedBase ← (NumberedWindowShiftAlgorithm.output 1 0 base).2
  let shiftedExtras ← (NumberedWindowShiftAlgorithm.output 1 0 extras).2
  let xs ← unpack shiftedExtras
  let binder := packNode 1 [dom,0]
  pure (packNode 2 [dom,packNode 5 [f,cod,label,shiftedBase,pack (xs ++ [binder])]])

def fabsRow (dst : Nat) (p : Nat × List Nat) :=
  let v (i : Nat) := p.2.getD i 0
  p.1 == 5 && v 2 != 0 && v 1 != 0 &&
    (NumberedWindowPairAlgorithm.decode (v 1).pred).any (fun t =>
      (freshBody (v 0) t.1 t.2 (v 2).pred (v 3) (v 4)).any (· == dst))

def fabs (q r : Nat) := guarded q r ((unpackNode q).any (fabsRow r))

def betaRows (dst : Nat) (p fn : Nat × List Nat) :=
  p.1 == 6 && fn.1 == 2 && p.2.getD 0 0 == fn.2.getD 0 0 &&
    ((NumberedWindowSingletonAlgorithm.output (p.2.getD 3 0) 0 (fn.2.getD 1 0)).1).any (· == dst)

def beta (q r : Nat) := guarded q r ((unpackNode q).any (fun p =>
  (unpackNode (p.2.getD 2 0)).any (betaRows r p)))

end LogicLineages.PersistentMarking.NumberedWindowBinderRootAlgorithm
