module
public import LogicLineages.PermittedControl.EntryEffectivityProof
public import LogicLineages.PermittedControl.EntryResiduesProof
public section
namespace LogicLineages.PermittedControl.StatementChecks
 theorem fixed_fullEntryEffectivity : Targets.EntryEffectivity := entryEffectivity
 theorem fixed_entryExistence : Targets.EntryExistenceOrbit := entryExistenceOrbit
 theorem fixed_entryResidues : Targets.EntryResidues := entryResidues
#print axioms fixed_fullEntryEffectivity
#print axioms fixed_entryExistence
#print axioms fixed_entryResidues
end LogicLineages.PermittedControl.StatementChecks
