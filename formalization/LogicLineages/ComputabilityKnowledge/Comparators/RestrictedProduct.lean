module

public import LogicLineages.ComputabilityKnowledge.PositiveExpression

@[expose] public section

/-!
# Independent specification of paper 02's bounded multiplication identity

This is the exact independently fixed statement of `lem:restricted-product`.
Its proof must be supplied separately; the specification proves no target. The
independent source domain is positive natural a,y,s,u,q. The expression
`2^a - 1` is ordinary natural subtraction; positivity of a makes this the
same positive Mersenne number used in the paper.
-/

namespace LogicLineages.ComputabilityKnowledge.Comparators.RestrictedProduct

open PositiveExpression

def FirstEquation (a s u : PosNat) : Prop :=
  2 ^ a.val * u.val + 1 = u.val + 2 ^ s.val

def SecondEquation (a y u q : PosNat) : Prop :=
  2 ^ a.val * q.val + y.val + 1 = u.val + q.val + 2 ^ a.val

def Target : Prop :=
  ∀ (a y s : PosNat), y.val < 2 ^ a.val - 1 →
    s.val < a.val * (2 ^ a.val - 1) →
      (s.val = a.val * y.val ↔
        ∃ u q : PosNat, FirstEquation a s u ∧ SecondEquation a y u q)

end LogicLineages.ComputabilityKnowledge.Comparators.RestrictedProduct
