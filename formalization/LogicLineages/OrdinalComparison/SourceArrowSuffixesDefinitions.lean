module
public import LogicLineages.OrdinalComparison.SourceSpecialApplicationDefinitions
@[expose] public section
/-! All ordered nonempty suffix decompositions of a simple type's right arrow
spine. This supplies the literal proper-subtype recursion indices, not the
recursive semantic domains themselves. -/
namespace LogicLineages.OrdinalComparison.Source.SourceArrowSuffixes

def arrowSuffixes : Ty → List (List Ty × Ty)
  | .ground => []
  | .arrow σ τ => ([σ], τ) :: (arrowSuffixes τ).map (fun p => (σ :: p.1, p.2))

def typeSize : Ty → Nat
  | .ground => 1
  | .arrow σ τ => 1 + typeSize σ + typeSize τ

end LogicLineages.OrdinalComparison.Source.SourceArrowSuffixes
