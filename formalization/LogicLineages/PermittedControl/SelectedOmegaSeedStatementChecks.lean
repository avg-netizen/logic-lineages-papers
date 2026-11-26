module
public import LogicLineages.PermittedControl.SelectedOmegaSeedProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_selectedOmegaSeed : SelectedOmegaSeedTargets.SelectedOmegaSeed :=
  SelectedOmegaSeed.Proof.selectedOmegaSeed
#print axioms fixed_selectedOmegaSeed
end LogicLineages.PermittedControl.StatementChecks
