module

public import LogicLineages.NativeModule.PersistentMarking.SharpAdmissibleStep
public import LogicLineages.NativeModule.PersistentMarking.SharpAdmissibleTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.SharpAdmissibleProof
open Spine SharpResults ExtendedMeasure
theorem prove (S : Signature) (n : Nat) : ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j :=
  Nat.strongRecOn (motive := fun n => ∀ j (h : ExtendedTree S j), treeSize h = n → Result S j) n
    (fun n ih j h hn => step S n (fun j' h' hlt => ih (treeSize h') hlt j' h' rfl) j h hn)

theorem weak : SharpAdmissibleTargets.Weak := by
  intro S q s t href he
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl q href

theorem strict : SharpAdmissibleTargets.Strict := by
  intro S q s t href he
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl q href

theorem matching : SharpAdmissibleTargets.Matching := by
  intro S qs ss ts href he
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href

theorem multiset : SharpAdmissibleTargets.Multiset := by
  intro S qs ss ts href he
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href

theorem coverage : SharpAdmissibleTargets.Coverage := by
  intro S qs ss ts href he
  obtain ⟨href⟩ := href
  obtain ⟨he⟩ := he
  exact prove S (treeSize he) _ he rfl qs href

theorem fullAdmissible : SharpAdmissibleTargets.FullAdmissible := ⟨weak,strict,matching,multiset,coverage⟩
end LogicLineages.PersistentMarking.SharpAdmissibleProof
