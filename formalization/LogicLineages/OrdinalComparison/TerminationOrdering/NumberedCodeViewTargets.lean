module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewTargets
open NumberedAuxiliaryCoding NumberedCodeView

def ActualViewRoundTrip : Prop := ∀ (n : Nat),
  (∀ code : Code (Fin n), unview (view code) = code) ∧
    (∀ data : CodeView n, view (unview data) = data)

/-- The domain keeps the previously accepted literal numeric Code presentation. -/
def ActualViewPrimitive : Prop := ∀ (n : Nat), Primrec (@view n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewTargets
