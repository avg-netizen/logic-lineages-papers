module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrier
open Source NumberedNumericCarrier NumberedLeastCodeRepresentative

/-- Type-indexed canonical syntax carrier, not the computability predicate C_tau. -/
def typedCanonicalCarrierTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (tau : Ty) (value : Nat) : Bool :=
  (decodeUniverse n arity symbols S Gamma value).any (fun q =>
    decide (q.1 = tau ∧ representativeCode symbols S q = value))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrier
