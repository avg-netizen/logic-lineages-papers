module
public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication
public import LogicLineages.PersistentMarking.NumberedWindowFreeAddress
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowTypedProbe
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressApplication (arrowView)
open NumberedWindowFreeAddress (freeAddress freshName)

/-- A typed address retains its own lexical context and has the indicated result type. -/
def typed (s : Settings) (type n : Nat) : Bool :=
  scalar s n && (addressView n).any (fun a => a.2.1 == type)

/-- Select the domain variable at one above the numeral bound of the canonical representative. -/
def probe (s : Settings) (n : Nat) : Option Nat :=
  if scalar s n then do
    let a ← addressView n
    let (domain,_) ← arrowView a.2.1
    return freeAddress a.1 domain (freshName a.2.2)
  else none
end LogicLineages.PersistentMarking.NumberedWindowTypedProbe
