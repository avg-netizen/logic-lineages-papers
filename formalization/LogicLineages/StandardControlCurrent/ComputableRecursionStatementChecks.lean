module
public import LogicLineages.StandardControlCurrent.ComputableRankedProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.ComputableRecursionStatementChecks
theorem full : ComputableRecursionTargets.Full :=
  ⟨ComputableFoldProof.listFold, ComputableRankedProof.ranked⟩
#print axioms full
end LogicLineages.StandardControlCurrent.ComputableRecursionStatementChecks
