module

public import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFreeAddress
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowCoverBoundsAlgorithm (bounds)

/-- A globally free variable in the original address format. The supplied
lexical context is kept as a field of the address. -/
def freeAddress (context : List Nat) (type name : Nat) : Nat :=
  packNode 3 [pack context,type,packNode 0 [type,name]]

/-- Use a name beyond every numeral occurring in the selected literal term. -/
def freshName (termCode : Nat) : Nat := (bounds termCode).1.2 + 1

end LogicLineages.PersistentMarking.NumberedWindowFreeAddress
