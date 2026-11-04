module
public import LogicLineages.OrdinalComparison.ParametricPairWorklistTargets
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.ProdSigma

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Proof

open ParametricFinitePairCollapse

/-- The row-major list has exactly the finite predecessor membership test. -/
theorem children_mem (G : Nat → Nat) (p q : Nat × Nat) :
    q ∈ children G p ↔ q ∈ predecessors G p := by
  rcases q with ⟨a, b⟩
  unfold children
  change (a, b) ∈ ((List.range (p.1 + 1)).product
      (List.range (G (pairNorm p) + 1))).filter
      (fun q => decide (Below q p ∧ pairNorm q ≤ G (pairNorm p))) ↔ _
  simp only [List.mem_filter, decide_eq_true_eq, predecessors, Finset.mem_filter]
  apply and_congr _ Iff.rfl
  constructor
  · intro h
    have h' := List.mem_product.mp h
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (List.mem_range.mp h'.1),
        Finset.mem_range.mpr (List.mem_range.mp h'.2)⟩
  · intro h
    have h' := Finset.mem_product.mp h
    exact List.mem_product.mpr
      ⟨List.mem_range.mpr (Finset.mem_range.mp h'.1),
        List.mem_range.mpr (Finset.mem_range.mp h'.2)⟩

/-- Distinct rows and columns remain distinct after the predecessor filter. -/
theorem children_nodup (G : Nat → Nat) (p : Nat × Nat) :
    (children G p).Nodup := by
  unfold children
  exact List.Nodup.filter _ (List.nodup_range.product List.nodup_range)

/-- Forgetting the traversal order recovers the frozen predecessor finset. -/
theorem children_toFinset (G : Nat → Nat) (p : Nat × Nat) :
    (children G p).toFinset = predecessors G p := by
  ext q
  simpa only [List.mem_toFinset] using children_mem G p q

theorem exactChildren : Targets.ExactChildren := by
  intro G p
  exact ⟨children_nodup G p, children_toFinset G p⟩

end LogicLineages.OrdinalComparison.Source.ParametricPairWorklist.Proof
