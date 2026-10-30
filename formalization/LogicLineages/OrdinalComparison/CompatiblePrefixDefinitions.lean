module
public import LogicLineages.OrdinalComparison.ConstantBudgetDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal least-monomial lower bound, stated using the actual CNF list. -/
def actualMinExponentAtLeast (k e : Ordinal.{0}) : Prop :=
  ∀ p : Ordinal × Ordinal, p ∈ Ordinal.CNF Ordinal.omega0 k → e ≤ p.1

/-- The source condition: each suffix monomial is at most every prefix monomial.
The empty zero prefix is allowed, and equality at the boundary is allowed. -/
def actualCNFPrefixCompatible (k r : Ordinal.{0}) : Prop :=
  ∀ p : Ordinal × Ordinal, p ∈ Ordinal.CNF Ordinal.omega0 k →
    ∀ q : Ordinal × Ordinal, q ∈ Ordinal.CNF Ordinal.omega0 r → q.1 ≤ p.1

def compensatedPrefixControl (c n : Nat) : Nat := Phi (c + n) - c

end LogicLineages.OrdinalComparison
