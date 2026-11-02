module
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationDefinitions
public import LogicLineages.OrdinalComparison.GroundCarrierTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport

def before (k : Nat) (left right : List Ty)
    (q : OrdinalExpression ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right)) :
    OrdinalExpression (Ty.curriedGround (k+1) :: ((Ty.ground :: left) ++ right)) :=
  SelectedAccountPreparation.prepare (Ty.ground :: left) right (Ty.curriedGround (k+1)) q

def after (k : Nat) (left right : List Ty)
    (q : OrdinalExpression (left ++ Ty.curriedGround (k+1) :: right)) :
    OrdinalExpression (Ty.curriedGround (k+1) :: (left ++ right)) :=
  SelectedAccountPreparation.prepare left right (Ty.curriedGround (k+1)) q
end LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport
