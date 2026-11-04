module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricActualCollapse

/-- Separate actual-ordinal maximum recursion; never replaces actualCollapse.
Outside epsilon zero the totalization is zero, with no source significance. -/
noncomputable def collapseWith (G : Nat → Nat) : Ordinal.{0} → Nat :=
  Ordinal.lt_wf.fix fun a rec =>
    if a < epsilonZero then
      (actualBoundedPredecessors a (G (actualOrdinalNorm a))).attach.sup
        (fun p => rec p.1 (by exact (Finset.mem_filter.mp p.2).2) + 1)
    else 0

/-- Independent universal characterization of the bounded predecessor maximum. -/
def Equation (G : Nat → Nat) (c : Ordinal.{0} → Nat) : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    (∀ b : Ordinal.{0}, b < a → actualOrdinalNorm b ≤ G (actualOrdinalNorm a) → c b+1 ≤ c a) ∧
    (∀ k : Nat, (∀ b : Ordinal.{0}, b < a →
      actualOrdinalNorm b ≤ G (actualOrdinalNorm a) → c b+1 ≤ k) → c a ≤ k)
end LogicLineages.OrdinalComparison.ParametricActualCollapse
