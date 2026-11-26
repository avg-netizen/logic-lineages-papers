module
public import LogicLineages.StandardControlCurrent.CounterExpansionTargets
public import LogicLineages.StandardControlCurrent.NumericalKernelProcessProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CounterExpansionProof
open OrdinalComparison NumericalKernel CounterExpansion

theorem input_le (d c t : Nat) : t ≤ value d c t :=
  iterate_self_le (fun x => (self_lt_Phi x).le) _ t

theorem entries_bounds (n c t : Nat) (ht : c+2*(n+3)+1 ≤ t) :
    ∀ p ∈ entries n c t, t ≤ p.2 ∧ 3 ≤ p.1 ∧ p.1 ≤ n+3 ∧ c+2*p.1+1 ≤ p.2 := by
  induction n generalizing t with
  | zero => intro p hp; simp only [entries,List.mem_singleton] at hp; subst p; simp only; omega
  | succ n ih =>
    intro p hp
    simp only [entries,List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only; omega
    · have hs := input_le (n+4) (c+n+4) t
      have h := ih (value (n+4) (c+n+4) t) (by omega) p hp
      exact ⟨hs.trans h.1,h.2.1,by omega,h.2.2.2⟩

theorem entries_eq (n c t : Nat) (ht : c+2*(n+3)+1 ≤ t) :
    entries n c t = CounterLeaderExpansion.entries n c t ∧
    bottomInput n c t = CounterLeaderExpansion.bottomInput n c t := by
  induction n generalizing t with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have hs := input_le (n+4) (c+n+4) t
    have h := ih (value (n+4) (c+n+4) t) (by omega)
    have he := (NumericalKernelProof.padded (n+4) (c+n+4) t (by omega) (by omega)).2
    change value (n+4) (c+n+4) t = CounterLeaderExpansion.kernel (n+4) (c+n+4) t at he
    rw [he] at h
    constructor
    · simpa only [entries,CounterLeaderExpansion.entries,h.1,he]
    · simpa only [bottomInput,CounterLeaderExpansion.bottomInput,h.2,he]

theorem bottom_le (n c t : Nat) : t ≤ bottomInput n c t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih => exact (input_le _ _ _).trans (ih _)

theorem ladder : CounterExpansionTargets.LadderCalibration := by
  intro n c t ht
  have hb := entries_bounds n c t ht
  have he := entries_eq n c t ht
  have hi := bottom_le n c t
  have hpre : leaderPreimage n c t = CounterLeaderExpansion.leaderPreimage n c t := by
    unfold leaderPreimage CounterLeaderExpansion.leaderPreimage
    rw [(NumericalKernelProof.padded 3 (c+3) (bottomInput n c t) (by omega) (by omega)).2,he.2]
    rfl
  refine ⟨hb,he.1,he.2,hpre,?_,?_⟩
  · simp only [leader,CounterLeaderExpansion.leader,hpre]
  · unfold residuals CounterLeaderExpansion.residuals
    rw [← he.1]
    apply List.map_congr_left
    intro p hp
    have h := hb p hp
    exact (NumericalKernelProof.padded p.1 (c+p.1) p.2 (by omega) (by omega)).1

theorem upper_bounds (k m c t : Nat) (ht : c+2*(m+k+3)+1 ≤ t) :
    ∀ p ∈ upperEntries k m c t, t ≤ p.2 ∧ m+3 < p.1 ∧ p.1 ≤ m+k+3 ∧ c+2*p.1+1 ≤ p.2 := by
  induction k generalizing t with
  | zero => simp only [upperEntries,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ k ih =>
    intro p hp
    simp only [upperEntries,List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp only; omega
    · have hs := input_le (m+k+4) (c+m+k+4) t
      have h := ih (value (m+k+4) (c+m+k+4) t) (by omega) p hp
      exact ⟨hs.trans h.1,h.2.1,by omega,h.2.2.2⟩

theorem upper_eq (k m c t : Nat) (ht : c+2*(m+k+3)+1 ≤ t) :
    alignedInput k m c t = CounterLeaderCollision.alignedInput k m c t ∧
    upperEntries k m c t = CounterLeaderCollision.upperEntries k m c t := by
  induction k generalizing t with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have hs := input_le (m+k+4) (c+m+k+4) t
    have h := ih (value (m+k+4) (c+m+k+4) t) (by omega)
    have he := (NumericalKernelProof.padded (m+k+4) (c+m+k+4) t (by omega) (by omega)).2
    change value (m+k+4) (c+m+k+4) t = CounterLeaderExpansion.kernel (m+k+4) (c+m+k+4) t at he
    rw [he] at h
    constructor
    · simpa only [alignedInput,CounterLeaderCollision.alignedInput,h.1,he]
    · simpa only [upperEntries,CounterLeaderCollision.upperEntries,h.2,he]

theorem upper : CounterExpansionTargets.UpperCalibration := by
  intro k m c t ht
  have hb := upper_bounds k m c t ht
  have he := upper_eq k m c t ht
  refine ⟨hb,he.1,he.2,?_⟩
  unfold upperResiduals CounterLeaderCollision.upperResiduals
  rw [← he.2]
  apply List.map_congr_left
  intro p hp
  have h := hb p hp
  exact (NumericalKernelProof.padded p.1 (c+p.1) p.2 (by omega) (by omega)).1
end LogicLineages.StandardControlCurrent.CounterExpansionProof
