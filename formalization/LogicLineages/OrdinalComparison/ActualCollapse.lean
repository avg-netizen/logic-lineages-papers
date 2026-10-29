module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseTargets
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete
public import LogicLineages.OrdinalComparison.FiniteCollapse

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem actualCollapse_mem (a : Ordinal) (ha : a < epsilonZero)
    (b : Nat) (x : Ordinal) :
    x ∈ actualBoundedPredecessors a b ↔ x < a ∧ actualOrdinalNorm x ≤ b := by
  classical
  simp only [actualBoundedPredecessors, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans ha, h.2⟩, h.1⟩⟩

private theorem actualCollapse_eq (a : Ordinal) (ha : a < epsilonZero) :
    actualCollapse a =
      (actualBoundedPredecessors a (Phi (actualOrdinalNorm a))).attach.sup
        (fun p => actualCollapse p.1 + 1) := by
  conv_lhs => rw [actualCollapse, WellFounded.fix_eq]
  simp only [if_pos ha]
  rfl

theorem actualCollapse_equation : Targets.ActualNormControlledCollapse actualCollapse := by
  intro a ha
  constructor
  · intro b hb hn
    have hm := (actualCollapse_mem a ha (Phi (actualOrdinalNorm a)) b).mpr ⟨hb, hn⟩
    rw [actualCollapse_eq a ha]
    exact Finset.le_sup (f := fun p => actualCollapse p.1 + 1)
      (Finset.mem_attach _ ⟨b, hm⟩)
  · intro k hk
    rw [actualCollapse_eq a ha]
    apply Finset.sup_le
    intro p _
    have hp := (actualCollapse_mem a ha (Phi (actualOrdinalNorm a)) p.1).mp p.2
    exact hk p.1 hp.1 hp.2

theorem actualCollapse_uniqueBelowEpsilonZero :
    Targets.ActualCollapseUniqueBelowEpsilonZero actualCollapse := by
  intro d hd a
  induction a using Ordinal.lt_wf.induction with
  | h a ih =>
      intro ha
      apply Nat.le_antisymm
      · apply (hd a ha).2
        intro b hb hn
        rw [ih b hb (hb.trans ha)]
        exact (actualCollapse_equation a ha).1 b hb hn
      · apply (actualCollapse_equation a ha).2
        intro b hb hn
        rw [← ih b hb (hb.trans ha)]
        exact (hd a ha).1 b hb hn

theorem actualCollapse_controlledStrictness :
    Targets.ActualCollapseControlledStrictness actualCollapse :=
  fun a ha => (actualCollapse_equation a ha).1

theorem actualCollapse_notationCorrespondence (a : NONote) :
    actualCollapse a.1.repr = collapse a := by
  have hs : Targets.NormControlledCollapse (fun n : NONote => actualCollapse n.1.repr) := by
    intro n
    have heq := actualCollapse_equation n.1.repr (normalRepresentationSound n)
    constructor
    · intro m hm hn
      apply heq.1 m.1.repr hm
      rw [actualOrdinalNorm_notationCorrespondence m, actualOrdinalNorm_notationCorrespondence n]
      exact hn
    · intro k hk
      apply heq.2 k
      intro x hx hn
      obtain ⟨m, hm⟩ := normalRepresentationComplete x (hx.trans (normalRepresentationSound n))
      have hmn : m < n := by change m.1.repr < n.1.repr; rwa [hm]
      have hnorm : Vendor.R1.treeWeight m.1 ≤ Phi (Vendor.R1.treeWeight n.1) := by
        rw [← actualOrdinalNorm_notationCorrespondence m,
          ← actualOrdinalNorm_notationCorrespondence n, hm]
        exact hn
      simpa only [hm] using hk m hmn hnorm
  exact congrFun (collapse_specification_unique _ _ hs collapse_specification) a

theorem actualCollapse_finiteValues : Targets.ActualCollapseFiniteValues actualCollapse := by
  intro n
  have h := actualCollapse_notationCorrespondence (NONote.ofNat n)
  rw [collapse_ofNat] at h
  change actualCollapse (ONote.ofNat n).repr = n at h
  rwa [ONote.repr_ofNat] at h

end LogicLineages.OrdinalComparison
