module
public import LogicLineages.PermittedControl.StandardOmegaSeedProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_standardOmegaSeed : StandardOmegaSeed.StandardOmegaSeed :=
  StandardOmegaSeed.Proof.standardOmegaSeed
#print axioms fixed_standardOmegaSeed
end LogicLineages.PermittedControl.StatementChecks
