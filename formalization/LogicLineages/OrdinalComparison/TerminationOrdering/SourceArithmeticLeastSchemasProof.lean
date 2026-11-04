module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasProof
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open PositiveArithmeticSchemas PositiveArithmeticLeastSchemas OrdinaryArithmeticCarrier OrdinaryArithmeticDirect

theorem actualSourceLeastSchemas : SourceArithmeticLeastSchemasTargets.ActualSourceLeastSchemas := by
  intro n arity Gamma
  obtain ⟨scalar,multiset,h⟩ := PositiveArithmeticOperatorsProof.sourcePositiveOperators n arity Gamma
  refine ⟨scalar,multiset,?_⟩
  intro context
  refine ⟨(fun P x => (h P context x).1),(fun P x => (h P context x).2),?_,?_,?_,?_⟩
  · exact PositiveArithmeticLeastSchemasProof.actualLeastClosureSchema scalar context
  · exact PositiveArithmeticLeastSchemasProof.actualLeastClosureSchema multiset context
  · exact PositiveArithmeticLeastSchemasProof.actualLeastLeastnessSchema scalar context
  · exact PositiveArithmeticLeastSchemasProof.actualLeastLeastnessSchema multiset context

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasProof
