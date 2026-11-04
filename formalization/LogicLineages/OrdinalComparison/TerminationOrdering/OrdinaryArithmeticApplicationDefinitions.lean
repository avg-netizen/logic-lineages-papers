module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplication
open Source OrdinaryArithmeticQuotient NumberedNumericDecoding NumberedNumericApplication

def decodedApplication (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain x y : Nat) : Option Nat := do
  let ctx ← Encodable.decode (α := Context n) context
  let sigma ← decodeType domain
  let tau ← decodeType codomain
  canonicalApplication n arity ctx.1.1 ctx.1.2 Gamma sigma tau x y

def applicationValue (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (v : List.Vector Nat 6) : Nat :=
  (decide (decodedApplication n arity Gamma (v.get 0) (v.get 1) (v.get 2) (v.get 3) (v.get 4) = some (v.get 5))).toNat

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplication
