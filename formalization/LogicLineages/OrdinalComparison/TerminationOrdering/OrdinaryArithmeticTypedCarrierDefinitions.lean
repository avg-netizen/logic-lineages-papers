module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrier
open Source OrdinaryArithmeticQuotient NumberedNumericDecoding NumberedTypedCarrier

def typedValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (v : List.Vector Nat 3) : Nat :=
  ((Encodable.decode (α := Context n) (v.get 0)).any (fun ctx =>
    (decodeType (v.get 1)).any (fun tau =>
      typedCanonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma tau (v.get 2)))).toNat

def encodedTyped (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context typ value : Nat) : Prop :=
  ∃ (ctx : Context n) (tau : Ty), Encodable.decode context = some ctx ∧
    decodeType typ = some tau ∧ typedCanonicalCarrierTest n arity ctx.1.1 ctx.1.2 Gamma tau value = true

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrier
