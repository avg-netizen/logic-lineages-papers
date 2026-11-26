module

public import LogicLineages.PersistentMarking.NumberedWindowOwnerAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSelectAlgorithm
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowOwnerAlgorithm (plan applyCopies)
open NumberedWindowAnnotationAlgorithm (annotations)
open NumberedWindowMarkRootAlgorithm (guarded)

def chosen (extra : Bool) (i base extras : Nat) : Option Nat :=
  (unpack (if extra then extras else base)).bind (fun xs => xs[i]?)

def fromOwner (extra : Bool) (i : Nat) (domains : List Nat) (dst f result label base extras : Nat) :=
  let route := plan result domains
  label != 0 && (chosen extra i base extras).any (fun q =>
    (annotations q).1 == route.1 && applyCopies f label.pred base extras q route.2 == dst)

def body (extra : Bool) (i : Nat) (domains : List Nat) (dst : Nat) (p : Nat × List Nat) :=
  let v (n : Nat) := p.2.getD n 0
  p.1 == 5 && fromOwner extra i domains dst (v 0) (v 1) (v 2) (v 3) (v 4)

def select (extra : Bool) (i : Nat) (domains : List Nat) (src dst : Nat) :=
  guarded src dst ((unpackNode src).any (body extra i domains dst))

end LogicLineages.PersistentMarking.NumberedWindowSelectAlgorithm
