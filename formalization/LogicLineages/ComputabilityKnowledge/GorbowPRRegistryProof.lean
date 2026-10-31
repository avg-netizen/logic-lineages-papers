module

public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.Proof
open GorbowPRProgram

private theorem occursOfMem {n : Nat} (p : Program n) (a : Packed)
    (h : a ∈ nodes p) : Occurs a p := by
  induction p with
  | zero => exact .here _ (List.mem_singleton.mp h)
  | succ => exact .here _ (List.mem_singleton.mp h)
  | projection i => exact .here _ (List.mem_singleton.mp h)
  | composition f g hf hg =>
      simp only [nodes, List.mem_cons, List.mem_append, List.mem_flatten, List.mem_ofFn] at h
      rcases h with h | h | ⟨l, ⟨i, rfl⟩, hi⟩
      · exact .here _ h
      · exact .compositionFunction f g (hf h)
      · exact .compositionArgument f g i (hg i hi)
  | recursion f g hf hg =>
      simp only [nodes, List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · exact .here _ h
      · exact .recursionBase f g (hf h)
      · exact .recursionStep f g (hg h)

private theorem memOfOccurs {n : Nat} {p : Program n} {a : Packed}
    (h : Occurs a p) : a ∈ nodes p := by
  induction h with
  | here p h =>
      subst a
      cases p <;> exact List.mem_cons_self
  | compositionFunction f g _ ih =>
      exact List.mem_cons_of_mem _ (List.mem_append_left _ ih)
  | compositionArgument f g i _ ih =>
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatten.mpr ⟨nodes (g i), List.mem_ofFn.mpr ⟨i,rfl⟩, ih⟩))
  | recursionBase f g _ ih =>
      exact List.mem_cons_of_mem _ (List.mem_append_left _ ih)
  | recursionStep f g _ ih =>
      exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)

theorem exactNodes : Targets.ExactNodes := by
  intro n p a
  exact ⟨occursOfMem p a, memOfOccurs⟩

theorem rootTag : Targets.RootTag := by
  intro n p
  cases p <;> rfl

theorem taggedCoverage : Targets.TaggedCoverage := by
  intro n p a
  constructor
  · intro h
    obtain ⟨tag, ht⟩ := List.mem_iff_getElem?.mp (memOfOccurs h)
    have hb : tag < (nodes p).length := by
      by_contra hn
      have he := List.getElem?_eq_none (l := nodes p) (Nat.le_of_not_gt hn)
      rw [ht] at he
      cases he
    exact ⟨tag, List.mem_range.mpr hb, ht⟩
  · rintro ⟨tag, _, ht⟩
    exact occursOfMem p a (List.mem_iff_getElem?.mpr ⟨tag,ht⟩)

theorem uniqueTags : Targets.UniqueTags := by
  intro n p
  exact List.nodup_range

theorem exactDispatch : Targets.ExactDispatch := by
  intro n p tag m q args h ht
  simp [dispatch, ht, h]

theorem invalidTag : Targets.InvalidTag := by
  intro n p tag args h
  simp [dispatch, List.getElem?_eq_none h]

theorem invalidArity : Targets.InvalidArity := by
  intro n p tag m q args ht h
  simp [dispatch, ht, h]

end LogicLineages.ComputabilityKnowledge.GorbowPRRegistry.Proof
