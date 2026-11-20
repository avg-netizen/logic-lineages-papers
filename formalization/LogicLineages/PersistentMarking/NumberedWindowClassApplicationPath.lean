module

public import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHop

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationPath
open NumberedWindowClassApplicationHop (liftHop)
open NumberedWindowFieldAlgorithm (pack unpack)

abbrev Accumulator := Nat × List Nat

/-- Accept a lifted hop only when its actual recomputed source code
matches the current image class. Collect the new hops in reverse order. -/
def advance (least : Nat → Option Nat) (domain result argument : Nat)
    (state : Option Accumulator) (oldHop : Nat) : Option Accumulator := do
  let (current,done) ← state
  let (source,target,hop) ← liftHop least domain result argument oldHop
  if source == current then some (target,hop :: done) else none

/-- Transform the supplied nonempty list of hops, anchored at the
starting image class, and repack the unchanged order of the new hops. -/
def liftPath (least : Nat → Option Nat) (domain result argument imageSource certificate : Nat) :
    Option (Nat × Nat) := do
  let hops ← unpack certificate
  if hops.isEmpty then none else
    let (target,done) ← hops.foldl (advance least domain result argument) (some (imageSource,[]))
    pure (target,pack done.reverse)

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationPath
