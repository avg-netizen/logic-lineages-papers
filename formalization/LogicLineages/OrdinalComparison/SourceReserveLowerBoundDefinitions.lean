module
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound
/-- The printed source bounds, not a restriction of the generated grammar.
Inactive sources and bare F have floor one; active applications have four;
active ground lambdas have five. Opaque free blocks retain unrestricted internals. -/
def sourceFloor {k Γ F n} (e : TrackedSource.Expr k Γ F n) : Int :=
  if TrackedSource.active e then
    match e with
    | .tracked => 1
    | .lam _ => 5
    | _ => 4
  else 1
end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound
