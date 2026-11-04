module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrier
open Source NumberedNumericCarrier

def listCarrierTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (values : List Nat) : Bool := values.all (canonicalCarrierTest n arity symbols S Gamma)

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrier
