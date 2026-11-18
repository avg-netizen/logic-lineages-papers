module
public import LogicLineages.PermittedControl.StandardFiniteQueryProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_standardFiniteQuery : StandardFiniteQuery.StandardFiniteQuery :=
  StandardFiniteQuery.Proof.selectedFiniteQuery
#print axioms fixed_standardFiniteQuery
end LogicLineages.PermittedControl.StatementChecks
