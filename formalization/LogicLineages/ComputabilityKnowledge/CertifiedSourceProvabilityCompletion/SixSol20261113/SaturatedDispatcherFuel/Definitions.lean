module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel
open GorbowSyntax
/-- Actual lineDispatcher call with unchanged index, history and encoded line.
Only its runtime fuel argument will vary. No well-formedness condition is built
into this acceptance predicate. -/
def acceptance {ctx : Nat} (tag : Nat) (index fuel history line : Term ctx) : Formula ctx :=
 .equal (HistoryDispatcher.dispatcherCall tag index fuel history line) (.succ .zero)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel
