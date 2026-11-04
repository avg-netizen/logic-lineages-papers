module
public import LogicLineages.OrdinalComparison.ParametricActualCollapseTargets
public import LogicLineages.OrdinalComparison.ActualCollapse
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricActualCollapse.Proof

private theorem predecessor_mem (a : Ordinal) (ha : a < epsilonZero)
    (b : Nat) (x : Ordinal) :
    x ∈ actualBoundedPredecessors a b ↔ x < a ∧ actualOrdinalNorm x ≤ b := by
  classical
  simp only [actualBoundedPredecessors, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨h.1.trans ha,h.2⟩,h.1⟩⟩

theorem recursion_eq (G : Nat → Nat) (a : Ordinal) (ha : a < epsilonZero) :
    collapseWith G a =
      (actualBoundedPredecessors a (G (actualOrdinalNorm a))).attach.sup
        (fun p => collapseWith G p.1+1) := by
  conv_lhs => rw [collapseWith, WellFounded.fix_eq]
  simp only [if_pos ha]
  rfl

theorem equation (G : Nat → Nat) : Equation G (collapseWith G) := by
  intro a ha
  constructor
  · intro b hb hn
    have hm := (predecessor_mem a ha (G (actualOrdinalNorm a)) b).mpr ⟨hb,hn⟩
    rw [recursion_eq G a ha]
    exact Finset.le_sup (f := fun p => collapseWith G p.1+1)
      (Finset.mem_attach _ ⟨b,hm⟩)
  · intro k hk
    rw [recursion_eq G a ha]
    apply Finset.sup_le
    intro p _
    have hp := (predecessor_mem a ha (G (actualOrdinalNorm a)) p.1).mp p.2
    exact hk p.1 hp.1 hp.2

theorem exactRecursion : Targets.ExactRecursion := fun G => ⟨equation G,recursion_eq G⟩

theorem uniqueBelowEpsilonZero : Targets.UniqueBelowEpsilonZero := by
  intro G c hc a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
      intro ha
      apply Nat.le_antisymm
      · apply (hc a ha).2
        intro b hb hn
        rw [ih b hb (hb.trans ha)]
        exact (equation G a ha).1 b hb hn
      · apply (equation G a ha).2
        intro b hb hn
        rw [← ih b hb (hb.trans ha)]
        exact (hc a ha).1 b hb hn

theorem exactPhiSpecialization : Targets.ExactPhiSpecialization := by
  intro a ha
  exact (uniqueBelowEpsilonZero Phi actualCollapse actualCollapse_equation a ha).symm
end LogicLineages.OrdinalComparison.ParametricActualCollapse.Proof
