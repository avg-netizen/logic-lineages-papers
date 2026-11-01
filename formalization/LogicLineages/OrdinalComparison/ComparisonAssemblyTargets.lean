module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualComparisonQueryNodeProgram : Prop := Computable₂ encodedComparisonQueryNode

def ActualComparisonQueryNodeCorrect : Prop := ∀ (q : ComparisonQuery) (table : ComparisonNodeTable),
  comparisonQueryTableCovers q table → actualComparisonQueryCorrect q (encodedComparisonQueryNode q table)

def ActualComparisonQueryAssemblyPrograms : Prop := Computable₂ encodedComparisonQueryLayer ∧
  Computable encodedComparisonQueryTable ∧ Computable encodedComparisonQueryResult ∧
  Computable₂ encodedOneVariableSignDecision

def ActualComparisonQueryResultCorrect : Prop := ∀ q : ComparisonQuery,
  actualComparisonQueryCorrect q (encodedComparisonQueryResult q)

def FullActualComparisonQueryAssembly : Prop := ActualComparisonQueryNodeProgram ∧
  ActualComparisonQueryNodeCorrect ∧ ActualComparisonQueryAssemblyPrograms ∧ ActualComparisonQueryResultCorrect

end LogicLineages.OrdinalComparison.Targets
