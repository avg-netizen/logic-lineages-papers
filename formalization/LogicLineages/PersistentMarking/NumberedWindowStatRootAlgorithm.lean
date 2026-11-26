module

public import LogicLineages.PersistentMarking.NumberedWindowCopyAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowStatAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatRootAlgorithm
open NumberedWindowCopyAlgorithm (Entries allowedTarget)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowStatAlgorithm (replacement)

def rows (xs : Entries) (heads : List Nat) (part : Nat) (q r : Nat × List Nat) :=
  let a (i : Nat) := q.2.getD i 0
  let g := r.2.getD 0 0
  q.1 == 5 && r.1 == 4 && a 2 != 0 &&
    (allowedTarget false xs heads (a 1) (a 0) g && replacement (a 3) part (r.2.getD 1 0))

def stat (xs : Entries) (heads : List Nat) (part src dst : Nat) :=
  guarded src dst ((unpackNode src).any (fun q => (unpackNode dst).any (rows xs heads part q)))
end LogicLineages.PersistentMarking.NumberedWindowStatRootAlgorithm
