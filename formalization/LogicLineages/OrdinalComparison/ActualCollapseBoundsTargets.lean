module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section

/-! Cited source supplier: Wilken--Weiermann Proposition 2.3, as stated in
paper 05 `foundations.tex`, lines 143–148. These are actual unary-collapse
bounds, not global monotonicity. Ordinary finite-tail addition and its exact
norm formula are separate prerequisites. No encoded effectiveness is asserted.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualFiniteTailClosureNorm : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ k : Nat,
    a + (k : Ordinal) < epsilonZero ∧
      actualOrdinalNorm (a + (k : Ordinal)) = actualOrdinalNorm a + k

def ActualCollapseDominatesNorm : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → actualOrdinalNorm a ≤ actualCollapse a

def ActualCollapseFiniteTailBound : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → ∀ k : Nat, k ≤ actualCollapse (a + (k : Ordinal))

end LogicLineages.OrdinalComparison.Targets
