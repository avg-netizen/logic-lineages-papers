module
public import LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Proof

private theorem histogram_wellFounded :
    ∀ n : Nat, WellFounded (ComparisonKernelHistogramLt n) := by
  intro n
  induction n with
  | zero => exact ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  | succ n ih =>
    exact (Prod.lex Nat.lt_wfRel ⟨ComparisonKernelHistogramLt n,ih⟩).wf

private theorem rangeHistogram_ext (n : Nat) :
    ∀ (first : Nat) (next current : WordPair),
      (∀ r, first ≤ r → r < first+n → rangeCount r next = rangeCount r current) →
      rangeHistogram n first next = rangeHistogram n first current := by
  induction n with
  | zero => intro first next current h; rfl
  | succ n ih =>
    intro first next current h
    change (rangeCount first next,rangeHistogram n (first+1) next) =
      (rangeCount first current,rangeHistogram n (first+1) current)
    apply Prod.ext
    · exact h first (Nat.le_refl _) (by omega)
    · exact ih (first+1) next current (by
        intro r hfirst hlast
        exact h r (by omega) (by omega))

private theorem rangeHistogram_lt (n : Nat) :
    ∀ (first : Nat) (next current : WordPair) (r : Nat),
      first ≤ r → r < first+n →
      rangeCount r next < rangeCount r current →
      (∀ s, first ≤ s → s < r → rangeCount s next = rangeCount s current) →
      ComparisonKernelHistogramLt n
        (rangeHistogram n first next) (rangeHistogram n first current) := by
  induction n with
  | zero => intro first next current r hfirst hlast hlt hlow; omega
  | succ n ih =>
    intro first next current r hfirst hlast hlt hlow
    change Prod.Lex Nat.lt (ComparisonKernelHistogramLt n)
      (rangeCount first next,rangeHistogram n (first+1) next)
      (rangeCount first current,rangeHistogram n (first+1) current)
    by_cases heq : r = first
    · subst r
      exact Prod.Lex.left _ _ hlt
    · have hcount : rangeCount first next = rangeCount first current :=
        hlow first (Nat.le_refl _) (by omega)
      rw [hcount]
      exact Prod.Lex.right _ (ih (first+1) next current r (by omega) (by omega) hlt (by
        intro s hs hsr
        exact hlow s (by omega) hsr))

/-- All entries in the finite occurrence-count measure agree. -/
theorem measure_ext (D : Nat) (next current : WordPair)
    (hE : counterCount next = counterCount current)
    (hR : ∀ r, 1 ≤ r → r ≤ rankBound D → rangeCount r next = rangeCount r current) :
    wordMeasure D next = wordMeasure D current := by
  apply Prod.ext
  · exact hE
  · exact rangeHistogram_ext (rankBound D) 1 next current (by
      intro r hr hlast
      exact hR r hr (by omega))

/-- Counter occurrences are the first coordinate, independently of all ranks. -/
theorem decrease_of_counter (D : Nat) (next current : WordPair)
    (h : counterCount next < counterCount current) : ChildDecrease D next current := by
  exact Prod.Lex.left _ _ h

/-- A strict decrease at the first differing positive rank suffices. -/
theorem decrease_of_rank (D : Nat) (next current : WordPair) (r : Nat)
    (hE : counterCount next = counterCount current)
    (hr : 1 ≤ r) (hD : r ≤ rankBound D)
    (hlt : rangeCount r next < rangeCount r current)
    (hlow : ∀ s, 1 ≤ s → s < r → rangeCount s next = rangeCount s current) :
    ChildDecrease D next current := by
  change Prod.Lex Nat.lt (ComparisonKernelHistogramLt (rankBound D))
    (counterCount next,rangeHistogram (rankBound D) 1 next)
    (counterCount current,rangeHistogram (rankBound D) 1 current)
  rw [hE]
  exact Prod.Lex.right _
    (rangeHistogram_lt (rankBound D) 1 next current r hr (by omega) hlt hlow)

theorem measureWellFounded : Targets.MeasureWellFounded := by
  intro D
  have hw : WellFounded (Prod.Lex Nat.lt (ComparisonKernelHistogramLt (rankBound D))) :=
    (Prod.lex Nat.lt_wfRel
      ⟨ComparisonKernelHistogramLt (rankBound D),histogram_wellFounded (rankBound D)⟩).wf
  exact InvImage.wf (wordMeasure D) hw

theorem countCriterion : Targets.CountCriterion := by
  intro D next current h
  rcases h with hE | ⟨hE,r,hr,hD,hlt,hlow⟩
  · exact decrease_of_counter D next current hE
  · exact decrease_of_rank D next current r hE hr hD hlt hlow

end LogicLineages.OrdinalComparison.GuardChildMeasureCompletion.Proof
