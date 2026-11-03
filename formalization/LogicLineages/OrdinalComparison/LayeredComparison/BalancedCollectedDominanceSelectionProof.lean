module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectedDominanceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedDominanceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance.Proof

set_option maxHeartbeats 200000

/-- A minimum is selected from the literal finite list, rather than supplied
as an additional hypothesis on the original comparison row. -/
private theorem minimum_member {α : Type*} (f : α → Nat) (xs : List α) :
    xs ≠ [] → ∃ a ∈ xs, ∀ b ∈ xs, f a ≤ f b := by
  induction xs with
  | nil =>
    intro hxs
    exact False.elim (hxs rfl)
  | cons a xs ih =>
    intro _
    by_cases hxs : xs = []
    · subst xs
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro b hb
      have hba : b = a := List.mem_singleton.mp hb
      subst b
      exact Nat.le_refl _
    · obtain ⟨c, hc, hmin⟩ := ih hxs
      by_cases hac : f a ≤ f c
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.le_refl _
        · exact hac.trans (hmin b hb)
      · refine ⟨c, List.mem_cons_of_mem a hc, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.le_of_lt (Nat.lt_of_not_ge hac)
        · exact hmin b hb

/-- The finite maximum below uses actual head values, never notation codes. -/
private theorem maximum_member {α : Type*} (f : α → Nat) (xs : List α) :
    xs ≠ [] → ∃ a ∈ xs, ∀ b ∈ xs, f b ≤ f a := by
  induction xs with
  | nil =>
    intro hxs
    exact False.elim (hxs rfl)
  | cons a xs ih =>
    intro _
    by_cases hxs : xs = []
    · subst xs
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro b hb
      have hba : b = a := List.mem_singleton.mp hb
      subst b
      exact Nat.le_refl _
    · obtain ⟨c, hc, hmax⟩ := ih hxs
      by_cases hca : f c ≤ f a
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.le_refl _
        · exact (hmax b hb).trans hca
      · refine ⟨c, List.mem_cons_of_mem a hc, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.le_of_lt (Nat.lt_of_not_ge hca)
        · exact hmax b hb

/-- The original, uncollected threshold supplies the entire collected row's
large-input condition because every representative is an original atom. -/
private theorem collected_large (basis : List Nat) (row : Row)
    (hlarge : ∀ a ∈ row.atoms, threshold row ≤ input basis a.2) :
    ∀ a ∈ (Collection.collect basis row).atoms,
      threshold (Collection.collect basis row) ≤ input basis a.2 := by
  intro a ha
  obtain ⟨q, hq⟩ := (Collection.Proof.collected_atom basis row a ha).2.2
  exact (Collection.Proof.originalThresholdBudget basis row).2.2.2.2.2.trans
    (hlarge (q, a.2) hq)

/-- Every actual greatest surviving key inherits the sign of the original
row, with nonzero coefficient and finite input minimum derived internally. -/
theorem everyGreatestSurvivorSign : Targets.EveryGreatestSurvivorSign := by
  intro basis row hf hg hlarge winner hwinner
  have support := Collection.Proof.literalCollectedSupport basis row
  have hnonzero := (support.2.1 winner hwinner.1).1
  have hnonempty : (Collection.collect basis row).atoms ≠ [] := by
    intro hempty
    have hm := hwinner.1
    rw [hempty] at hm
    cases hm
  obtain ⟨selected, hs, hmin⟩ := minimum_member
    (fun a : Int × Atom => input basis a.2)
    (Collection.collect basis row).atoms hnonempty
  have hsign := DominanceProof.actualDominance basis (Collection.collect basis row)
    (support.2.2.1 hf) (support.2.2.2 hg) support.1
    (collected_large basis row hlarge) selected hs hmin
    winner hwinner.1 hnonzero hwinner.2
  rw [(Collection.Proof.exactCollectedValue basis row).2.2.1] at hsign
  exact ⟨hnonzero, hsign⟩

/-- Cancellation retains the complete original remainder. Otherwise the
actual value maximum is greatest for the actual head/complete-input key. -/
theorem actualCollectedDichotomy : Targets.ActualCollectedDichotomy := by
  intro basis row hf hg hlarge
  by_cases hempty : (Collection.collect basis row).atoms = []
  · exact Or.inl ⟨hempty,
      (Collection.Proof.exactCollectedValue basis row).2.2.2.2 hempty⟩
  · have support := Collection.Proof.literalCollectedSupport basis row
    obtain ⟨selected, hs, hmin⟩ := minimum_member
      (fun a : Int × Atom => input basis a.2)
      (Collection.collect basis row).atoms hempty
    have keys := KeyProof.actualKeyWindow basis (Collection.collect basis row)
      (support.2.2.1 hf) (support.2.2.2 hg)
      (collected_large basis row hlarge) selected hs hmin
    obtain ⟨winner, hwinner, hmax⟩ := maximum_member
      (fun a : Int × Atom => atomValue basis a.2)
      (Collection.collect basis row).atoms hempty
    have greatest : GreatestSurvivor basis row winner := by
      refine ⟨hwinner, ?_⟩
      intro a ha hless
      have hv := (keys winner hwinner a ha).1.mpr hless
      exact (Nat.not_lt_of_ge (hmax a ha)) hv
    exact Or.inr ⟨winner, greatest,
      everyGreatestSurvivorSign basis row hf hg hlarge winner greatest⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance.Proof
