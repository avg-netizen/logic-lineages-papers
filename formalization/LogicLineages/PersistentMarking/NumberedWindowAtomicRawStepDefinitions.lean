module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicRawStep
open NumberedWindowFieldAlgorithm (packNode)

/-- These are raw terms, not their enclosing tag-3 scalar addresses. -/
def freeRaw (type name : Nat) : Nat := packNode 0 [type,name]
def bottomRaw (type : Nat) : Nat := packNode 3 [type]

/-- Exact raw root certificate for the original bottom rule; the
outer raw-context wrapper is a separate encoding. -/
def bottomRoot : Nat := packNode 7 []

end LogicLineages.PersistentMarking.NumberedWindowAtomicRawStep
