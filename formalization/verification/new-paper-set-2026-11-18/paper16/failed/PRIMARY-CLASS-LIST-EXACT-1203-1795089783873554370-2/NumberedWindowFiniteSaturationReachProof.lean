import LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationBoundProof

namespace LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationReachProof
open NumberedWindowFiniteSaturation NumberedWindowFiniteSaturationBasicProof
open NumberedWindowFiniteSaturationBoundProof
universe u

private theorem finiteSound {α : Type u} (V : List α) (same edge : α → α → Bool) (seed : α)
    (he : EqualityTest same) (n : Nat) :
    ∀ v, v ∈ rounds V same edge seed n → GraphReach V edge seed v := by
  induction n with
  | zero =>
    intro v hv
    rcases (seedMem he).mp hv with ⟨hv,rfl⟩
    exact .start hv
  | succ n ih =>
    intro v hv
    have ha : v ∈ advance V same edge (rounds V same edge seed n) := hv
    obtain ⟨hV,w,hw,hr⟩ := (advanceMem he).mp ha
    rcases hr with rfl | hstep
    · exact ih _ hw
    · exact .next (ih _ hw) hV hstep

private theorem finiteComplete {α : Type u} (V : List α) (same edge : α → α → Bool)
    (seed v : α) (he : EqualityTest same) (h : GraphReach V edge seed v) :
    v ∈ saturate V same edge seed := by
  induction h with
  | start hV =>
    have hs : seed ∈ rounds V same edge seed 0 := (seedMem he).mpr ⟨hV,rfl⟩
    exact roundsMono V same edge seed he (Nat.zero_le V.length) hs
  | @next w v _ hv hstep ih =>
    have ha : v ∈ advance V same edge (saturate V same edge seed) :=
      (advanceMem he).mpr ⟨hv,w,ih,Or.inr hstep⟩
    rw [bound V same edge seed he] at ha
    exact ha

theorem reach {α : Type u} (V : List α) (same edge : α → α → Bool)
    (seed v : α) (he : EqualityTest same) :
    v ∈ saturate V same edge seed ↔ GraphReach V edge seed v :=
  ⟨finiteSound V same edge seed he V.length v,finiteComplete V same edge seed v he⟩

end LogicLineages.PersistentMarking.NumberedWindowFiniteSaturationReachProof
