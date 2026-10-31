module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumerationTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration.Proof

theorem pairsComplete : Targets.PairsComplete := by
  intro α β xs ys x y hx hy
  exact List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

theorem setsExact : Targets.SetsExact := by
  intro α _ xs
  induction xs with
  | nil =>
      intro s
      constructor
      · intro h
        have he : s = ∅ := by simpa [sets] using h
        subst s
        simp
      · intro h
        have he : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
          intro x hx
          exact List.not_mem_nil (h x hx))
        simp [he, sets]
  | cons a xs ih =>
      intro s
      rw [sets, List.mem_append]
      constructor
      · rintro (h | h)
        · intro x hx
          exact List.mem_cons_of_mem a ((ih s).mp h x hx)
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a ((ih u).mp hu x hx)
      · intro h
        by_cases ha : a ∈ s
        · right
          apply List.mem_map.mpr
          refine ⟨s.erase a, (ih _).mpr ?_, Finset.insert_erase ha⟩
          intro x hx
          have hm := Finset.mem_erase.mp hx
          exact (List.mem_cons.mp (h x hm.2)).resolve_left hm.1
        · left
          apply (ih s).mpr
          intro x hx
          have hn : x ≠ a := by intro he; subst x; exact ha hx
          exact (List.mem_cons.mp (h x hx)).resolve_left hn

theorem functionsComplete : Targets.FunctionsComplete := by
  intro n α xs f hf
  apply List.mem_map.mpr
  refine ⟨fun i _ => f i, ?_, rfl⟩
  exact (List.mem_pi xs _).mpr (fun i _ => hf i)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration.Proof
