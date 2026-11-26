import LogicLineages.PersistentMarking.TwoEnvironmentStep
namespace LogicLineages.PersistentMarking.TwoEnvironmentProof
open Spine TwoEnvironmentSupport ExtendedMeasure

theorem prove (S : Signature) (n : Nat) : ∀ j (h : ExtendedTree S j), treeSize h = n →
    ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ j :=
  Nat.strongRecOn (motive := fun n => ∀ j (h : ExtendedTree S j), treeSize h = n →
    ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ j) n
    (fun n ih j h hn => step S n (fun j' h' hlt => ih (treeSize h') hlt j' h' rfl) j h hn)

theorem weak : TwoEnvironmentTargets.Weak := by
  intro S γ δ hg hd he s t h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he
theorem strict : TwoEnvironmentTargets.Strict := by
  intro S γ δ hg hd he s t h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he
theorem matching : TwoEnvironmentTargets.Matching := by
  intro S γ δ hg hd he ss ts h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he
theorem multiset : TwoEnvironmentTargets.Multiset := by
  intro S γ δ hg hd he ss ts h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he
theorem coverage : TwoEnvironmentTargets.Coverage := by
  intro S γ δ hg hd he ss ts h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he
theorem whole : TwoEnvironmentTargets.Whole := by
  intro S γ δ hg hd he f base extras ts h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he
theorem ordered : TwoEnvironmentTargets.Ordered := by
  intro S γ δ hg hd he ss ts h
  obtain ⟨h⟩ := h
  exact prove S (treeSize h) _ h rfl γ δ hg hd he

theorem fullTwoEnvironments : TwoEnvironmentTargets.FullTwoEnvironments :=
  ⟨weak,strict,matching,multiset,coverage,whole,ordered⟩
end LogicLineages.PersistentMarking.TwoEnvironmentProof
