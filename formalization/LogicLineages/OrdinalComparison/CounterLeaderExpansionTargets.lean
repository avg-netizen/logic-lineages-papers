module
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderExpansion.Targets

/-- The actual descending entries, including the cubic last entry. All block
and residual domains are derived from one explicit computable source tail. -/
def ExactEntryDomains : Prop := ∀ n c t : Nat, threshold n c ≤ t →
  (entries n c t).map Prod.fst = (List.range (n+1)).reverse.map (fun i => i+3) ∧
  (entries n c t).getLast? = some (3, bottomInput n c t) ∧
  t ≤ bottomInput n c t ∧ t ≤ leaderPreimage n c t ∧
  (∀ p ∈ entries n c t, 3 ≤ p.1 ∧ p.1 ≤ n+3 ∧
    t ≤ p.2 ∧ c+2*p.1+1 ≤ p.2) ∧
  (residuals n c t).length = n+1

/-- Literal source counter expansion, in integers so that the fixed negative
correction is not silently truncated. Evenness and the quadratic subtraction
bound are conclusions. No half-leader bounds or collision theorem is assumed. -/
def ExactCounterLeaderIdentity : Prop := ∀ n c t : Nat, threshold n c ≤ t →
  Even (leader n c t) ∧ (c+1)/2 ≤ leader n c t / 2 ∧
  (count (n+3) c t : Int) =
    (leader n c t / 2 : Nat) + 1 - ((c+1)/2 : Nat) +
      ((residuals n c t).sum : Int)

end LogicLineages.OrdinalComparison.CounterLeaderExpansion.Targets
