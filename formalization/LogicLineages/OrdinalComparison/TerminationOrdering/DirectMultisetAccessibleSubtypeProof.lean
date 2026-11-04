module
public import LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeProof
open DirectMultisetAccessibleSubtype DirectMultisetPresentation DirectMultisetAccessibleSubtypeSupportProof

theorem directMemberClosure : DirectMultisetAccessibleSubtypeTargets.DirectMemberClosure := by
  intro α R source target hsource h
  obtain ⟨kept, removed, inserted, hs, ht, hn, hd⟩ := h
  obtain ⟨hk, hr, hi⟩ := witnessAccessible R source kept removed inserted hsource hs hd
  intro a ha
  rcases List.mem_append.mp (ht.mem_iff.mp ha) with ha | ha
  · exact hk a ha
  · exact hi a ha

theorem occurrencePreservingLift : DirectMultisetAccessibleSubtypeTargets.OccurrencePreservingLift := by
  intro α R xs h
  exact liftList R xs h

theorem exactLiftedDirect : DirectMultisetAccessibleSubtypeTargets.ExactLiftedDirect := by
  intro α R source target
  unfold AccessibleElement at source target
  constructor
  · rintro ⟨kept, removed, inserted, hs, ht, hn, hd⟩
    refine ⟨kept.map Subtype.val, removed.map Subtype.val, inserted.map Subtype.val,
      ?_, ?_, ?_, ?_⟩
    · exact (List.map_append (f := Subtype.val) (l₁ := kept) (l₂ := removed)) ▸ hs.map Subtype.val
    · exact (List.map_append (f := Subtype.val) (l₁ := kept) (l₂ := inserted)) ▸ ht.map Subtype.val
    · intro hz
      exact hn (List.map_eq_nil_iff.mp hz)
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      obtain ⟨a, ha, hr⟩ := hd b hb
      exact ⟨a.val, List.mem_map.mpr ⟨a, ha, rfl⟩, hr⟩
  · rintro ⟨kept, removed, inserted, hs, ht, hn, hd⟩
    have hsource : MembersAccessible R (source.map Subtype.val) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact b.property
    obtain ⟨hk, hr, hi⟩ := witnessAccessible R (source.map Subtype.val)
      kept removed inserted hsource hs hd
    obtain ⟨ks, hks⟩ := liftList R kept hk
    obtain ⟨rs, hrs⟩ := liftList R removed hr
    obtain ⟨is, his⟩ := liftList R inserted hi
    refine ⟨ks, rs, is, ?_, ?_, ?_, ?_⟩
    · apply (List.map_perm_map_iff Subtype.val_injective).mp
      have he : (ks ++ rs).map Subtype.val = kept ++ removed :=
        List.map_append.trans (congrArg₂ List.append hks hrs)
      exact he.symm ▸ hs
    · apply (List.map_perm_map_iff Subtype.val_injective).mp
      have he : (ks ++ is).map Subtype.val = kept ++ inserted :=
        List.map_append.trans (congrArg₂ List.append hks his)
      exact he.symm ▸ ht
    · intro hz
      apply hn
      rw [← hrs, hz]
      rfl
    · intro y hy
      have hy' : y.val ∈ inserted := by
        rw [← his]
        exact List.mem_map.mpr ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hrel⟩ := hd y.val hy'
      rw [← hrs] at ha
      obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
      refine ⟨b, hb, ?_⟩
      show R b.val y.val
      simpa only [hba] using hrel

end LogicLineages.OrdinalComparison.TerminationOrdering.DirectMultisetAccessibleSubtypeProof
