module

public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawApplicationLift
open NumberedWindowFieldAlgorithm (packNode)

/-- Wrap the original ordered raw step in the function slot of an auxiliary
application, using the identical argument numeral at both endpoints. -/
def lift (domain result argument source certificate target : Nat) : Nat × Nat × Nat :=
  (packNode 6 [domain,result,source,argument],
    packNode 5 [certificate],
    packNode 6 [domain,result,target,argument])

end LogicLineages.PersistentMarking.NumberedWindowRawApplicationLift
