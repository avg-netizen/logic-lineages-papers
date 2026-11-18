module
public import LogicLineages.CartierObserverCurrent.FullSinglePredecessorTargets
public import LogicLineages.OrdinalComparison.ParametricActualCollapseRecursionProof
public import LogicLineages.OrdinalComparison.ActualLimitPredecessor
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullSinglePredecessor
open LogicLineages.OrdinalComparison
open LogicLineages.OrdinalComparison.ParametricActualCollapse

/- Generic-control port of the actual ordinal maximum argument. The original
Phi-only proof remains untouched; every control use below is discharged by
StrictMono/inflation, and the collapse equation is proved independently. -/
private theorem controlledStrictness (f : Nat → Nat) (a : Ordinal.{0})
    (ha : a < epsilonZero) (b : Ordinal.{0}) (hb : b < a)
    (hn : actualOrdinalNorm b ≤ f (actualOrdinalNorm a)) :
    collapseWith f b + 1 ≤ collapseWith f a :=
  (ParametricActualCollapse.equation f a ha).1 b hb hn

private theorem actual_finite_tail (a : Ordinal) (ha : a < epsilonZero) (n : Nat) :
    a + (n : Ordinal) < epsilonZero ∧
      actualOrdinalNorm (a + (n : Ordinal)) = actualOrdinalNorm a + n := by
  obtain ⟨r, hr⟩ := normalRepresentationComplete a ha
  have ht := (finiteTailCorrect r n).1
  rw [hr] at ht
  constructor
  · rw [← ht]
    exact normalRepresentationSound (finiteTail r n)
  · rw [← ht, actualOrdinalNorm_notationCorrespondence (finiteTail r n),
      (finiteTailCorrect r n).2, ← actualOrdinalNorm_notationCorrespondence r, hr]

private theorem actual_finite_interval (a x : Ordinal) (n : Nat)
    (hax : a ≤ x) (hx : x < a + (n : Ordinal)) :
    ∃ j : Nat, j < n ∧ x = a + (j : Ordinal) := by
  have hd : x - a < (n : Ordinal) := by
    apply (add_lt_add_iff_left a).mp
    rwa [Ordinal.add_sub_cancel_of_le hax]
  obtain ⟨j, hj⟩ := Ordinal.eq_natCast_of_le_natCast hd.le
  refine ⟨j, ?_, ?_⟩
  · rw [hj] at hd
    exact_mod_cast hd
  · rw [← hj]
    exact (Ordinal.add_sub_cancel_of_le hax).symm

theorem genericRecurrence : Targets.GenericRecurrence := by
  intro f hf hinfl a ha hlim n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let b := f (actualOrdinalNorm a + n)
      let eta := actualMaximumPredecessor a b
      have hm := actualMaximumPredecessor_correct a hlim.bot_lt ha b
      have hs : actualOrdinalNorm eta = b := actualLimitMaximumPredecessorSaturation a ha hlim b
      have heps : eta < epsilonZero := hm.1.1.trans ha
      have ht := actual_finite_tail a ha n
      change collapseWith f (a + (n : Ordinal)) = collapseWith f eta + 1
      apply Nat.le_antisymm
      · apply (ParametricActualCollapse.equation f _ ht.1).2
        intro x hx hn
        have hnb : actualOrdinalNorm x ≤ b := by
          simpa only [ht.2] using hn
        by_cases hxa : x < a
        · have hxe : x ≤ eta := hm.2 ⟨hxa, hnb⟩
          rcases lt_or_eq_of_le hxe with hlt | heq
          · have hncontrol : actualOrdinalNorm x ≤ f (actualOrdinalNorm eta) := by
              rw [hs]
              exact hnb.trans (hinfl b).le
            exact (controlledStrictness f eta heps x hlt hncontrol).trans
              (Nat.le_succ _)
          · rw [heq]
        · obtain ⟨j, hj, heq⟩ := actual_finite_interval a x n (le_of_not_gt hxa) hx
          let bj := f (actualOrdinalNorm a + j)
          let etaj := actualMaximumPredecessor a bj
          have hjb : bj < b := hf (Nat.add_lt_add_left hj _)
          have hje : etaj < eta := actualLimitMaximumPredecessorStrictGrowth a ha hlim hjb
          have hnj : actualOrdinalNorm etaj = bj :=
            actualLimitMaximumPredecessorSaturation a ha hlim bj
          have hncontrol : actualOrdinalNorm etaj ≤ f (actualOrdinalNorm eta) := by
            rw [hnj, hs]
            exact hjb.le.trans (hinfl b).le
          have hc := controlledStrictness f eta heps etaj hje hncontrol
          rw [heq, ih j hj]
          exact Nat.add_le_add_right hc 1
      · apply controlledStrictness f _ ht.1 eta
          (hm.1.1.trans_le le_self_add)
        rw [ht.2, hs]


theorem completePredecessor : Targets.CompletePredecessor :=
  ⟨ParametricActualCollapse.exactRecursion, ParametricActualCollapse.exactPhiSpecialization,
    genericRecurrence⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullSinglePredecessor
end LogicLineages.CartierObserverCurrent.FullSinglePredecessor
