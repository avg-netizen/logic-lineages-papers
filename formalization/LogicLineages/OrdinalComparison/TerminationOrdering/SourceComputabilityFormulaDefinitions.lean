module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormula
open Source OrdinaryArithmeticTypedCarrier OrdinaryArithmeticApplication
open NumberedLeastCodeRepresentative

/-- Type recursion over actual partial canonical application. P interprets the unary base predicate. -/
def Computable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (P : Nat → Prop) (context : Nat) : Ty → Nat → Prop
  | .ground, x => encodedTyped n arity Gamma context (typeNumber .ground) x ∧ P x
  | .arrow sigma tau, x =>
      encodedTyped n arity Gamma context (typeNumber (.arrow sigma tau)) x ∧
      ∀ u : Nat, Computable n arity Gamma P context sigma u →
        ∃ z : Nat, decodedApplication n arity Gamma context (typeNumber sigma) (typeNumber tau) x u = some z ∧
          Computable n arity Gamma P context tau z

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormula
