module

public import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLift
public import LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationHop
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowPositivePathAlgorithm (hopView)

/-- Keep both original edge representatives and the witness. Recompute
both image class codes from the lifted literal terms in the result fiber. -/
def liftHop (least : Nat → Option Nat) (domain result argument code : Nat) :
    Option (Nat × Nat × Nat) := do
  let (_,source,witness,target) ← hopView code
  let (q,w,r) := NumberedWindowRawApplicationLift.lift domain result argument source witness target
  let sourceCode ← least q
  let targetCode ← least r
  pure (sourceCode,targetCode,packNode 2 [targetCode,packNode 1 [q,r,w]])

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationHop
