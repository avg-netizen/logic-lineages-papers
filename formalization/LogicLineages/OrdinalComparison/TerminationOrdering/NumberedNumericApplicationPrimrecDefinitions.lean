module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrec
open Source NumberedNumericCarrier NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedAuxiliaryDecoding

/-- First-order assembly and checked decoding replaces dependent output casts. -/
def applicationProgram (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma tau : Ty) (x y : Nat) : Option Nat := do
  let f ← decodeUniverse n arity symbols S Gamma x
  let a ← decodeUniverse n arity symbols S Gamma y
  if f.1 = .arrow sigma tau ∧ a.1 = sigma ∧
      representativeCode symbols S f = x ∧ representativeCode symbols S a = y then
    let result ← decodePacked arity Gamma (tau,Code.app sigma (termCode f.2) (termCode a.2))
    pure (representativeCode symbols S result)
  else none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationPrimrec
