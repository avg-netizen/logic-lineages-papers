module

public import LogicLineages.NativeModule.PersistentMarking.ConservativeStep

@[expose] public section

namespace LogicLineages.PersistentMarking.ConservativeProof
open Spine ConservativeResults ExtendedMeasure
theorem prove (S : Signature) (n : Nat) : ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j :=
  Nat.strongRecOn (motive := fun n => ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j) n
    (fun n ih j h hn => step S n (fun j' h' hlt => ih (treeSize h') hlt j' h' rfl) j h hn)

theorem weak : ConservativeTargets.Weak := by
  intro S q s t href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl q href ho

theorem strict : ConservativeTargets.Strict := by
  intro S q s t href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl q href ho

theorem matching : ConservativeTargets.Matching := by
  intro S qs ss ts href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href ho

theorem multiset : ConservativeTargets.Multiset := by
  intro S qs ss ts href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href ho

theorem coverage : ConservativeTargets.Coverage := by
  intro S qs ss ts href he ho
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href ho

theorem fullConservative : ConservativeTargets.FullConservative := ⟨weak,strict,matching,multiset,coverage⟩
end LogicLineages.PersistentMarking.ConservativeProof
