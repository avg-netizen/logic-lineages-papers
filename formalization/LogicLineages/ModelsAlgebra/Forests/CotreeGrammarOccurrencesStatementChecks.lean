module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrencesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences.StatementChecks

theorem wordMembership : Targets.WordMembership := Proof.wordMembership

theorem wordNodup : Targets.WordNodup := Proof.wordNodup

theorem occurrencePermutation : Targets.OccurrencePermutation := Proof.occurrencePermutation

theorem typeWordReindex : Targets.TypeWordReindex := Proof.typeWordReindex

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences
