module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowOuterShape
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowScalarAlgorithm (Settings canonical)

/-- Return the original term tag only for an admitted canonical address. -/
def outerShape (s : Settings) (n : Nat) : Option Nat := do
  let a ← addressView n
  if canonical s a then (unpackNode a.2.2).map Prod.fst else none

end LogicLineages.PersistentMarking.NumberedWindowOuterShape
