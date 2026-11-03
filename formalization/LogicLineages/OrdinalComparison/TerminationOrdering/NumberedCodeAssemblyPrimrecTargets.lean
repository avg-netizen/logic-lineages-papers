module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecTargets

/-- Assemble the original constructor and all its fields under the accepted literal Code presentation. -/
def ActualUnviewPrimitive : Prop := ∀ n : Nat,
  Primrec (@NumberedCodeView.unview n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecTargets
