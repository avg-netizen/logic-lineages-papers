import LogicLineages.PersistentMarking.NumberedWindowFiniteSaturation

namespace LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationBasicProof
open NumberedWindowFiniteSaturation
open scoped List
universe u

theorem seedMem {α : Type u} {V : List α} {same edge : α → α → Bool} {seed v : α}
    (he : EqualityTest same) :
    v ∈ rounds V same edge seed 0 ↔ v ∈ V ∧ seed = v := by
  simp only [rounds,List.mem_filter,he seed v]

theorem advanceMem {α : Type u} {V A : List α} {same edge : α → α → Bool} {v : α}
    (he : EqualityTest same) :
    v ∈ advance V same edge A ↔ v ∈ V ∧ ∃ w, w ∈ A ∧ (w = v ∨ edge w v = true) := by
  simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true]
  constructor
  · rintro ⟨hv,w,hw,h⟩
    exact ⟨hv,w,hw,h.elim (fun e => .inl ((he w v).mp e)) Or.inr⟩
  · rintro ⟨hv,w,hw,h⟩
    exact ⟨hv,w,hw,h.elim (fun e => .inl ((he w v).mpr e)) Or.inr⟩

theorem roundsSub {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    (n : Nat) : rounds V same edge seed n <+ V := by
  cases n with
  | zero => exact List.filter_sublist
  | succ n => exact List.filter_sublist

private theorem monotoneFilter {α : Type u} (p q : α → Bool) (V : List α)
    (h : ∀ v, v ∈ V → p v = true → q v = true) :
    V.filter p <+ V.filter q := by
  induction V with
  | nil => exact .slnil
  | cons a vs ih =>
    have htail : vs.filter p <+ vs.filter q :=
      ih (fun v hv hp => h v (List.mem_cons_of_mem a hv) hp)
    by_cases hp : p a = true
    · have hq := h a List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp,List.filter_cons_of_pos hq]
      exact .cons_cons a htail
    · by_cases hq : q a = true
      · rw [List.filter_cons_of_neg hp,List.filter_cons_of_pos hq]
        exact .cons a htail
      · rw [List.filter_cons_of_neg hp,List.filter_cons_of_neg hq]
        exact htail

private theorem monotoneAdvance {α : Type u} (V A B : List α) (same edge : α → α → Bool)
    (h : A ⊆ B) : advance V same edge A <+ advance V same edge B := by
  unfold advance
  apply monotoneFilter
  intro v _ hp
  obtain ⟨w,hw,he⟩ := List.any_eq_true.mp hp
  exact List.any_eq_true.mpr ⟨w,h hw,he⟩

theorem roundsStep {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    (he : EqualityTest same) (n : Nat) :
    rounds V same edge seed n <+ rounds V same edge seed (n+1) := by
  induction n with
  | zero =>
    change V.filter (same seed) <+ advance V same edge (V.filter (same seed))
    unfold advance
    apply monotoneFilter
    intro v hv hp
    have hz : v ∈ V.filter (same seed) := List.mem_filter.mpr ⟨hv,hp⟩
    exact List.any_eq_true.mpr
      ⟨v,hz,Bool.or_eq_true_iff.mpr (Or.inl ((he v v).mpr rfl))⟩
  | succ n ih =>
    change advance V same edge (rounds V same edge seed n) <+
      advance V same edge (rounds V same edge seed (n+1))
    exact monotoneAdvance V _ _ same edge ih.subset

theorem roundsMono {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    (he : EqualityTest same) {i j : Nat} (hle : i ≤ j) :
    rounds V same edge seed i ⊆ rounds V same edge seed j := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => intro _ h; exact h
  | succ d ih =>
    intro _ h
    exact (roundsStep V same edge seed he (i+d)).subset (ih h)

end LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationBasicProof
