module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrier
open Source OrdinaryArithmeticQuotient NumberedNumericCarrier QuotientDirectCarrier

def scalarValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (v : List.Vector Nat 2) : Nat :=
  ((Encodable.decode (α := Context n) (v.get 0)).any (fun ctx =>
    canonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma (v.get 1))).toNat

def listValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (v : List.Vector Nat 2) : Nat :=
  ((Encodable.decode (α := Context n) (v.get 0)).any (fun ctx =>
    (Encodable.decode (α := List Nat) (v.get 1)).any
      (listCarrierTest n arity ctx.1.1 ctx.1.2 Gamma))).toNat

def encodedScalar (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context value : Nat) : Prop :=
  ∃ ctx : Context n, Encodable.decode context = some ctx ∧
    canonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma value = true

def encodedList (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context value : Nat) : Prop :=
  ∃ (ctx : Context n) (values : List Nat), Encodable.decode context = some ctx ∧
    Encodable.decode value = some values ∧ listCarrierTest n arity ctx.1.1 ctx.1.2 Gamma values = true

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrier
