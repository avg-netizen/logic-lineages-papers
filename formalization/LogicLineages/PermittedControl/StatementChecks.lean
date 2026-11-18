module
public import LogicLineages.PermittedControl.NearControlProof

@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks

theorem fixed_nearControlModular : Targets.NearControlModular := nearControlModular
theorem fixed_nearControlOrbit : Targets.NearControlOrbit := nearControlOrbit

#print axioms fixed_nearControlModular
#print axioms fixed_nearControlOrbit
end LogicLineages.PermittedControl.StatementChecks
