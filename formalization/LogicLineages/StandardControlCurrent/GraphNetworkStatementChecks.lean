module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Proof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetworkStatementChecks
 theorem full : GraphNetwork.Targets.FullGraphDomains := GraphNetwork.Proof.full
#print axioms full
end LogicLineages.StandardControlCurrent.GraphNetworkStatementChecks
