module
public import LogicLineages.OrdinalComparison.CNFDescent

public import Mathlib.SetTheory.Cardinal.ToNat

@[expose] public section

/-! The source additive norm by actual ordinal well-founded CNF recursion.

Paper 05, `foundations.tex`, `def:norm`: charge every monomial with its full
finite coefficient (via its finite cardinal) times one plus the recursively computed exponent norm.
The definition uses actual ordinal CNF and actual ordinal descent, not a
chosen notation representative. The value zero outside epsilon zero is only
a total-function convention; no source claim concerns that outside domain.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def actualOrdinalNorm : Ordinal.{0} → Nat :=
  Ordinal.lt_wf.fix fun a rec =>
    if ha : a < epsilonZero then
      ((Ordinal.CNF Ordinal.omega0 a).attach.map fun p =>
        p.1.2.card.toNat * (1 + rec p.1.1 (cnfDescentBelowEpsilonZero a ha p.1 p.2).1)).sum
    else 0

end LogicLineages.OrdinalComparison
