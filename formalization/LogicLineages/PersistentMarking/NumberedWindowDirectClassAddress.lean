module

public import LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectClassAddress
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowFieldAlgorithm (pack packNode)

/-- Convert the supplied literal class-edge certificate into a positive
path of exactly one hop to the target's original least code. -/
def singleHop (target certificate : Nat) : Nat :=
  pack [packNode 2 [target,certificate]]

def directAddress (positive : Nat → Nat → Nat → Bool)
    (source certificate target : Nat) : Bool :=
  (addressView target).any (fun a => positive source (singleHop a.2.2 certificate) target)

end LogicLineages.PersistentMarking.NumberedWindowDirectClassAddress
