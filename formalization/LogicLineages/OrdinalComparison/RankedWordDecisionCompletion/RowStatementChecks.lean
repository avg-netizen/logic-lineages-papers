module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks

theorem exact_row_normalization : Targets.ExactRowNormalization :=
  Proof.exactRowNormalization

theorem residual_word_syntax : Targets.ResidualWordSyntax :=
  Proof.residualWordSyntax

theorem residual_word_values : Targets.ResidualWordValues :=
  Proof.residualWordValues

theorem exact_source_counter_expansion : Targets.ExactSourceCounterExpansion :=
  Proof.exactSourceCounterExpansion

#print axioms exact_row_normalization
#print axioms residual_word_syntax
#print axioms residual_word_values
#print axioms exact_source_counter_expansion

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.StatementChecks
