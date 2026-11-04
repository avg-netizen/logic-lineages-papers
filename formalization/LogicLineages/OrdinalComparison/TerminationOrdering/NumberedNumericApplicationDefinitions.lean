module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplication
open Source NumberedRewriteSyntax NumberedNumericCarrier NumberedLeastCodeRepresentative NumberedQuotientApplication

def canonicalApplication (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma tau : Ty) (x y : Nat) : Option Nat := do
  let f ← decodeUniverse n arity symbols S Gamma x
  let a ← decodeUniverse n arity symbols S Gamma y
  if hf : f.1 = .arrow sigma tau then
    if ha : a.1 = sigma then
      if representativeCode symbols S f = x ∧ representativeCode symbols S a = y then
        pure (representativeCode symbols S (applicationPacked (hf ▸ f.2) (ha ▸ a.2)))
      else none
    else none
  else none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplication
