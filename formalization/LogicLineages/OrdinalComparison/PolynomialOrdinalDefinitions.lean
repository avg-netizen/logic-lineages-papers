module
public import LogicLineages.OrdinalComparison.ConstantBudgetDefinitions
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal decreasing-CNF polynomial whose coordinate i is the coefficient
of omega^i. Zero coefficients are omitted, without changing other parts. -/
def polynomialRawNote : (d : Nat) → (Fin d → Nat) → ONote
  | 0, _ => 0
  | d + 1, a =>
      if h : a (Fin.last d) = 0 then polynomialRawNote d (Fin.init a)
      else ONote.oadd (ONote.ofNat d) ⟨a (Fin.last d), Nat.pos_of_ne_zero h⟩
        (polynomialRawNote d (Fin.init a))

end LogicLineages.OrdinalComparison
