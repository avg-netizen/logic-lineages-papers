module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplication
open NumberedWindowAddressAlgorithm (Address addressView)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowScalarAlgorithm (Settings canonical least)

def arrowView : Nat → Option (Nat × Nat)
  | 0 => none
  | n+1 => NumberedWindowPairAlgorithm.decode n

def applyAddresses (s : Settings) (q u : Address) : Option Nat := do
  let (domain,result) ← arrowView q.2.1
  if canonical s q && canonical s u && (q.1 == u.1) && (domain == u.2.1) then
    let term := packNode 6 [domain,result,q.2.2,u.2.2]
    (least s q.1 result term).map (fun k => packNode 3 [pack q.1,result,k])
  else none

def application (s : Settings) (source argument : Nat) : Option Nat := do
  let q ← addressView source
  let u ← addressView argument
  applyAddresses s q u

def graph (s : Settings) (source argument value : Nat) : Bool :=
  application s source argument == some value

end LogicLineages.PersistentMarking.NumberedWindowAddressApplication
