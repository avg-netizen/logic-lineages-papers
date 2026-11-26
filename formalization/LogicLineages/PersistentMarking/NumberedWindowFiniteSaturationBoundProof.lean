import LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationBasicProof

namespace LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationBoundProof
open NumberedWindowFiniteSaturation NumberedWindowFiniteSaturationBasicProof
universe u

private theorem stableNext {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    (n : Nat) (h : rounds V same edge seed n = rounds V same edge seed (n+1)) :
    rounds V same edge seed (n+1) = rounds V same edge seed ((n+1)+1) := by
  change advance V same edge (rounds V same edge seed n) =
    advance V same edge (rounds V same edge seed (n+1))
  rw [h]

private theorem stableThrough {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    {i j : Nat} (hle : i ≤ j)
    (h : rounds V same edge seed i = rounds V same edge seed (i+1)) :
    rounds V same edge seed j = rounds V same edge seed (j+1) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => exact h
  | succ d ih => exact stableNext V same edge seed (i+d) ih

theorem bound {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    (he : EqualityTest same) :
    advance V same edge (saturate V same edge seed) = saturate V same edge seed := by
  apply Classical.byContradiction
  intro hn
  have nofix : ∀ i, i ≤ V.length →
      rounds V same edge seed i ≠ rounds V same edge seed (i+1) := by
    intro i hle h
    exact hn (stableThrough V same edge seed hle h).symm
  have grows : ∀ i, i ≤ V.length + 1 → i ≤ (rounds V same edge seed i).length := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have hle : i ≤ V.length := by omega
      have hl : i ≤ (rounds V same edge seed i).length := ih (by omega)
      have hs := roundsStep V same edge seed he i
      have hln := hs.length_le
      have hne : (rounds V same edge seed i).length ≠
          (rounds V same edge seed (i+1)).length := by
        intro hm
        exact nofix i hle (hs.eq_of_length hm)
      omega
  have hg := grows (V.length+1) (Nat.le_refl _)
  have hmax := (roundsSub V same edge seed (V.length+1)).length_le
  omega

end LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationBoundProof
