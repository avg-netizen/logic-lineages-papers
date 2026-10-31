module

public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.Proof
open GorbowPRProgram GorbowPRRegistry

private def Good (xs : List Packed) : Prop :=
  ∀ (tag : Nat) (a : Packed), xs[tag]? = some a →
    ∃ before after : List Packed,
      xs = before ++ nodes a.2 ++ after ∧ before.length = tag

private theorem goodNil : Good [] := by
  intro tag a h
  simp at h

private theorem goodAppend (xs ys : List Packed) (hx : Good xs) (hy : Good ys) :
    Good (xs ++ ys) := by
  intro tag a h
  by_cases ht : tag < xs.length
  · have hlocal : xs[tag]? = some a := by
      simpa only [List.getElem?_append_left ht] using h
    obtain ⟨before, after, he, hb⟩ := hx tag a hlocal
    exact ⟨before, after ++ ys, by simp [he, List.append_assoc], hb⟩
  · have hle : xs.length ≤ tag := Nat.le_of_not_gt ht
    have hlocal : ys[tag - xs.length]? = some a := by
      simpa only [List.getElem?_append_right hle] using h
    obtain ⟨before, after, he, hb⟩ := hy _ a hlocal
    refine ⟨xs ++ before, after, by simp [he, List.append_assoc], ?_⟩
    simp only [List.length_append]
    omega

private theorem goodFlatten (xs : List (List Packed))
    (h : ∀ x ∈ xs, Good x) : Good xs.flatten := by
  induction xs with
  | nil => exact goodNil
  | cons x xs ih =>
      exact goodAppend x xs.flatten (h x (by simp))
        (ih (fun y hy => h y (by simp [hy])))

private theorem goodRoot {n : Nat} (p : Program n) (children : List Packed)
    (he : nodes p = ⟨n,p⟩ :: children) (hc : Good children) : Good (nodes p) := by
  intro tag a h
  cases tag with
  | zero =>
      have ha : a = ⟨n,p⟩ := by simpa [he] using h.symm
      subst a
      exact ⟨[], [], by simp, rfl⟩
  | succ tag =>
      have hl : children[tag]? = some a := by simpa [he] using h
      obtain ⟨before, after, hb, hlen⟩ := hc tag a hl
      refine ⟨⟨n,p⟩ :: before, after, ?_, ?_⟩
      · simp [he, hb]
      · simp [hlen]

private theorem allGood {n : Nat} (p : Program n) : Good (nodes p) := by
  induction p with
  | zero => exact goodRoot .zero [] rfl goodNil
  | succ => exact goodRoot .succ [] rfl goodNil
  | projection i => exact goodRoot (.projection i) [] rfl goodNil
  | composition f g hf hg =>
      apply goodRoot (.composition f g) _ rfl
      apply goodAppend _ _ hf
      apply goodFlatten
      intro xs hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hg i
  | recursion f g hf hg =>
      exact goodRoot (.recursion f g) _ rfl (goodAppend _ _ hf hg)

theorem nodeBlocks : Targets.NodeBlocks := by
  intro n p tag a h
  exact allGood p tag a h

theorem lookupTransport : Targets.LookupTransport := by
  intro n p tag a localTag b ht hl
  obtain ⟨before, after, he, hlen⟩ := nodeBlocks n p tag a ht
  have hbound : localTag < (nodes a.2).length := by
    by_contra hn
    have hn' := List.getElem?_eq_none (l := nodes a.2) (Nat.le_of_not_gt hn)
    rw [hl] at hn'
    cases hn'
  rw [he, List.append_assoc]
  rw [List.getElem?_append_right (show before.length ≤ tag + localTag by omega)]
  rw [hlen, Nat.add_sub_cancel_left, List.getElem?_append_left hbound]
  exact hl

end LogicLineages.ComputabilityKnowledge.GorbowPRSubtree.Proof
