module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorTargets
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem mem_actualBoundedPredecessors (a : Ordinal) (ha : a < epsilonZero)
    (b : Nat) (x : Ordinal) :
    x ∈ actualBoundedPredecessors a b ↔ x < a ∧ actualOrdinalNorm x ≤ b := by
  classical
  simp only [actualBoundedPredecessors, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans ha, h.2⟩, h.1⟩⟩

theorem actualMaximumPredecessor_correct :
    Targets.ActualMaximumPredecessorCorrect actualMaximumPredecessor := by
  classical
  intro a hpos ha b
  have hz : actualOrdinalNorm 0 = 0 := by
    exact actualOrdinalNorm_notationCorrespondence (0 : NONote)
  have hs : (actualBoundedPredecessors a b).Nonempty :=
    ⟨0, (mem_actualBoundedPredecessors a ha b 0).mpr ⟨hpos, by rw [hz]; exact Nat.zero_le b⟩⟩
  have heq : actualMaximumPredecessor a b = (actualBoundedPredecessors a b).max' hs := by
    apply le_antisymm
    · exact Finset.sup_le fun x hx => Finset.le_max' _ x hx
    · exact Finset.le_sup (f := id) (Finset.max'_mem _ hs)
  rw [heq]
  refine ⟨(mem_actualBoundedPredecessors a ha b _).mp (Finset.max'_mem _ hs), ?_⟩
  intro x hx
  exact Finset.le_max' _ x ((mem_actualBoundedPredecessors a ha b x).mpr hx)

theorem actualMaximumPredecessor_unique :
    Targets.ActualMaximumPredecessorUnique actualMaximumPredecessor := by
  intro a hpos ha b x hx
  exact hx.unique (actualMaximumPredecessor_correct a hpos ha b)

theorem actualMaximumPredecessor_notationCorrespondence :
    Targets.ActualMaximumPredecessorNotationCorrespondence actualMaximumPredecessor := by
  intro a hpos b
  apply actualMaximumPredecessor_unique a.1.repr hpos (normalRepresentationSound a) b
  have hm := maximumPredecessor_correct a b hpos
  refine ⟨⟨hm.1.1, ?_⟩, ?_⟩
  · rw [actualOrdinalNorm_notationCorrespondence]
    exact hm.1.2
  · intro x hx
    obtain ⟨n, hn⟩ := normalRepresentationComplete x (hx.1.trans (normalRepresentationSound a))
    have hnlt : n < a := by change n.1.repr < a.1.repr; rw [hn]; exact hx.1
    have hnb : Vendor.R1.treeWeight n.1 ≤ b := by
      rw [← actualOrdinalNorm_notationCorrespondence n, hn]
      exact hx.2
    have hle := hm.2 ⟨hnlt, hnb⟩
    change n.1.repr ≤ (maximumPredecessor a b).1.repr at hle
    rwa [hn] at hle

end LogicLineages.OrdinalComparison
