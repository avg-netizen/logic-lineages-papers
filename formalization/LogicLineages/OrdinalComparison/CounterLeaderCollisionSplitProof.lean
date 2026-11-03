module
public import LogicLineages.OrdinalComparison.CounterLeaderCollisionTargets
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionEntriesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterLeaderCollision.Proof
open CounterLeaderExpansion

private theorem entries_split (k m c t : Nat) :
    entries (m+k) c t = upperEntries k m c t ++
      entries m c (alignedInput k m c t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simpa only [Nat.add_succ, Nat.add_zero, Nat.add_eq, entries, upperEntries, alignedInput,
      List.cons_append, Nat.add_assoc] using
      congrArg (fun es : List (Nat × Nat) => (m+k+4,t) :: es)
        (ih (kernel (m+k+4) (c+m+k+4) t))

private theorem bottomInput_split (k m c t : Nat) :
    bottomInput (m+k) c t = bottomInput m c (alignedInput k m c t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simpa only [Nat.add_succ, Nat.add_zero, Nat.add_eq, bottomInput, alignedInput,
      Nat.add_assoc] using
      ih (kernel (m+k+4) (c+m+k+4) t)

private theorem alignedInput_ge (k m c t : Nat) :
    t ≤ alignedInput k m c t := by
  induction k generalizing t with
  | zero => exact le_rfl
  | succ k ih =>
    exact (CounterLeaderExpansion.Proof.kernel_ge _ _ _).trans (ih _)

private theorem upperEntries_length (k m c t : Nat) :
    (upperEntries k m c t).length = k := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => simp only [upperEntries, List.length_cons, ih]

private theorem upperEntries_rank_gt (k m c t : Nat) :
    ∀ p ∈ upperEntries k m c t, m+3 < p.1 := by
  induction k generalizing t with
  | zero =>
    intro p hp
    simp only [upperEntries, List.not_mem_nil] at hp
  | succ k ih =>
    intro p hp
    rcases List.mem_cons.mp hp with he | hm
    · subst p
      change m+3 < m+k+4
      omega
    · exact ih _ p hm

theorem exactChainSplitting : Targets.ExactChainSplitting := by
  intro k m c t ht
  have hs := entries_split k m c t
  have hb := bottomInput_split k m c t
  have hge := alignedInput_ge k m c t
  have hlower : threshold m c ≤ alignedInput k m c t := by
    dsimp [threshold] at ht ⊢
    omega
  refine ⟨hs,hb,?_,hge,hlower,upperEntries_length k m c t,?_,?_⟩
  · simp only [leader, leaderPreimage, hb]
  · intro p hp
    have hm : p ∈ entries (m+k) c t := by
      rw [hs]
      exact List.mem_append_left _ hp
    have hd :=
      (CounterLeaderExpansion.Proof.exactEntryDomains (m+k) c t ht).2.2.2.2.1 p hm
    exact ⟨upperEntries_rank_gt k m c t p hp,hd.2.1,hd.2.2.1,hd.2.2.2⟩
  · dsimp only [residuals, upperResiduals]
    rw [hs, List.map_append]

end LogicLineages.OrdinalComparison.CounterLeaderCollision.Proof
