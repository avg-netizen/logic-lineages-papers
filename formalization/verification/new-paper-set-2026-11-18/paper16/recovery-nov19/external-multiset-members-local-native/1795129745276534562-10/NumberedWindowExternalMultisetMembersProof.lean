import LogicLineages.PersistentMarking.NumberedWindowExternalMultisetUnionProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalMultisetMembersProof
open NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowArithmeticFields NumberedWindowExternalIDOperators
open NumberedWindowExternalMultisetClosureTargets NumberedWindowExternalMultisetUnionProof

private theorem empty (S : Spine.Signature) (K : List Ty) :
    Least (multisetStep S K) (encodeFields []) := by
  apply (coded_iff S K []).mpr
  refine ⟨by simp [TypedAddressList], Acc.intro [] ?_⟩
  intro target h
  obtain ⟨_, _, kept, removed, added, hSource, _, hNonempty, _⟩ := h
  exact (hNonempty (List.append_eq_nil_iff.mp hSource.symm.eq_nil).2).elim

private theorem listOfSingletons (S : Spine.Signature) (K : List Ty) (xs : List Nat)
    (h : ∀ a ∈ xs, Least (multisetStep S K) (encodeFields [a])) :
    Least (multisetStep S K) (encodeFields xs) := by
  induction xs with
  | nil => exact empty S K
  | cons a rest ih =>
    exact union S K [a] rest (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem singletonDescendants {S K a target}
    (h : AddressDirect S K [a] target) : ∀ b ∈ target, AddressPositive S K a b := by
  obtain ⟨_, _, kept, removed, added, hSource, hTarget, hNonempty, hDom⟩ := h
  have hEmpty : kept = [] := by
    cases kept with
    | nil => rfl
    | cons k rest =>
      have hTail : [] = rest ++ removed := (List.cons.inj hSource.singleton_eq).2
      exact (hNonempty (List.nil_eq_append_iff.mp hTail).2).elim
  intro b hb
  have hAdded : b ∈ added := by
    simpa only [hEmpty, List.nil_append] using hTarget.mem_iff.mp hb
  obtain ⟨d, hRemoved, hStep⟩ := hDom b hAdded
  have hOne : d ∈ [a] := hSource.mem_iff.mpr (List.mem_append_right _ hRemoved)
  exact (List.mem_singleton.mp hOne) ▸ hStep

theorem singleton : ExternalISingleton := by
  intro S K a ha
  obtain ⟨hTyped, hAcc⟩ :=
    ((NumberedWindowExternalIDAccProof.actualAcc S K a).1).mp ha
  revert hTyped
  induction hAcc with
  | intro a _ ih =>
    intro hTyped
    apply (coded_iff S K [a]).mpr
    refine ⟨?_, Acc.intro [a] ?_⟩
    · intro b hb
      exact (List.mem_singleton.mp hb).symm ▸ hTyped
    · intro target hReplace
      have hMembers : ∀ b ∈ target, Least (multisetStep S K) (encodeFields [b]) :=
        fun b hb => ih b (singletonDescendants hReplace b hb) (hReplace.2.1 b hb)
      exact ((coded_iff S K target).mp (listOfSingletons S K target hMembers)).2

theorem finite : ExternalIFiniteMultiset := by
  intro S K xs h
  exact listOfSingletons S K xs (fun a ha => singleton S K a (h a ha))

end LogicLineages.PersistentMarking.NumberedWindowExternalMultisetMembersProof
