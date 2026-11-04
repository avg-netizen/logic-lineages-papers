module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricActualCollapse.Targets

def ExactRecursion : Prop := ∀ G : Nat → Nat,
  Equation G (collapseWith G) ∧ ∀ a : Ordinal.{0}, a < epsilonZero →
    collapseWith G a = (actualBoundedPredecessors a (G (actualOrdinalNorm a))).attach.sup
      (fun p => collapseWith G p.1+1)

def UniqueBelowEpsilonZero : Prop := ∀ (G : Nat → Nat) (c : Ordinal.{0} → Nat),
  Equation G c → ∀ a : Ordinal.{0}, a < epsilonZero → c a = collapseWith G a

def ExactPhiSpecialization : Prop := ∀ a : Ordinal.{0},
  a < epsilonZero → collapseWith Phi a = actualCollapse a

def FiniteValues : Prop := ∀ G : Nat → Nat,
  (∀ n : Nat, n ≤ G n) → ∀ n : Nat, collapseWith G (n : Ordinal.{0}) = n
end LogicLineages.OrdinalComparison.ParametricActualCollapse.Targets
