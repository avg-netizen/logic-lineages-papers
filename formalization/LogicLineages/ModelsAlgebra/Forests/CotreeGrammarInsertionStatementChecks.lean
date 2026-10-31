module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion.StatementChecks

theorem cycleInsertOccurrence : Targets.CycleInsertOccurrence := Proof.cycleInsertOccurrence

theorem cycleInsertProduction : Targets.CycleInsertProduction := Proof.cycleInsertProduction

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion
