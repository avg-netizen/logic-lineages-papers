module
public import LogicLineages.PermittedControl.StandardSourceFactsProof
@[expose] public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_standardSourceFacts : StandardSourceFactsTargets.StandardSourceFacts :=
  StandardSourceFacts.Proof.standardSourceFacts
#print axioms fixed_standardSourceFacts
end LogicLineages.PermittedControl.StatementChecks
