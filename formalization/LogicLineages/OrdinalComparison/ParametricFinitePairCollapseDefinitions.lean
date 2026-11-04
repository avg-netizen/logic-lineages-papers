module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions
public import Mathlib.Data.Finset.Prod
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse
noncomputable def ordinal (p : Nat × Nat) : Ordinal.{0} :=
  Ordinal.omega0*(p.1 : Ordinal)+(p.2 : Ordinal)
def pairNorm (p : Nat × Nat) : Nat := 2*p.1+p.2
def Below (p q : Nat × Nat) : Prop := p.1<q.1 ∨ (p.1=q.1 ∧ p.2<q.2)
instance (p q : Nat × Nat) : Decidable (Below p q) := inferInstanceAs (Decidable (_ ∨ _))
/-- Exact finite rectangle and tests; no sufficient-budget approximation. -/
def predecessors (G : Nat → Nat) (p : Nat × Nat) : Finset (Nat × Nat) :=
  ((Finset.range (p.1+1)).product (Finset.range (G (pairNorm p)+1))).filter
    (fun q => Below q p ∧ pairNorm q ≤ G (pairNorm p))
noncomputable def value (G : Nat → Nat) (p : Nat × Nat) : Nat :=
  ParametricActualCollapse.collapseWith G (ordinal p)
end LogicLineages.OrdinalComparison.Source.ParametricFinitePairCollapse
