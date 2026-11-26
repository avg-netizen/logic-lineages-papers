module
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceInterfaceStatementChecks
theorem full : PolicySourceInterfaceTargets.Full :=
  ⟨DefaultSourceDomainProof.domain,PolicySourceInterfaceProof.programs,
    PolicySourceInterfaceProof.heads,PolicySourceInterfaceProof.typed,PolicySourceInterfaceProof.raw⟩
#print axioms full
end LogicLineages.StandardControlCurrent.PolicySourceInterfaceStatementChecks
