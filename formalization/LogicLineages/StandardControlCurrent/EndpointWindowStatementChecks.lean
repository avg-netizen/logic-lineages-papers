module
public import LogicLineages.StandardControlCurrent.EndpointWindowTargets
public import LogicLineages.OrdinalComparison.HeadWindowProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.EndpointWindowStatementChecks
open OrdinalComparison

theorem endpoints : EndpointWindowTargets.FullActualSparseEndpointComparison :=
  fullActualSparseEndpointComparison

theorem headWindow : EndpointWindowTargets.FullActualDifferentHeadWindow :=
  fullActualDifferentHeadWindow

#print axioms endpoints
#print axioms headWindow

end LogicLineages.StandardControlCurrent.EndpointWindowStatementChecks
