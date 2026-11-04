module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticAccessibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibility
open OrdinaryArithmeticQuotient

def DecodedSubtypeClosed (n : Nat) (context : Nat) : Prop :=
  ∃ ctx : Context n, Encodable.decode context = some ctx ∧ SubtypeClosed (fun tau => tau ∈ ctx.1.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibility
