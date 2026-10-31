module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem walker_ordinal_coding : Targets.walkerOrdinalCoding := by
  intro ξ _
  letI := Encodable.ofCountable ξ.ToType
  refine ⟨?_, rfl, ?_⟩
  · intro s t h
    apply Subtype.ext
    exact Encodable.encode_injective h
  · rintro ⟨l, hl⟩ t ht
    cases l with
    | nil => simp [walkerOrdinalParent] at ht
    | cons a l =>
      have he : (⟨l, hl.tail⟩ : WalkerOrdinalNode ξ) = t := Option.some.inj ht
      subst t
      change Encodable.encode l < Encodable.encode (a :: l)
      rw [Encodable.encode_list_cons]
      exact Nat.lt_succ_of_le (Nat.right_le_pair _ _)

theorem walker_ordinal_parent_height : Targets.walkerOrdinalParentHeight := by
  intro ξ s t ht
  rcases s with ⟨l, hl⟩
  cases l with
  | nil => simp [walkerOrdinalParent] at ht
  | cons a l =>
    have he : (⟨l, hl.tail⟩ : WalkerOrdinalNode ξ) = t := Option.some.inj ht
    subst t
    cases l with
    | nil => exact Ordinal.typein_lt_self a
    | cons b l =>
      apply (Ordinal.typein_lt_typein (α := ξ.ToType) (· < ·)).mpr
      exact List.rel_of_pairwise_cons hl (by simp)

theorem walker_ordinal_children : Targets.walkerOrdinalChildren := by
  intro ξ s β hβ
  rcases s with ⟨l, hl⟩
  have htop : walkerOrdinalHeight ξ ⟨l, hl⟩ ≤ ξ := by
    cases l with
    | nil => exact le_rfl
    | cons a l => exact (Ordinal.typein_lt_self a).le
  have hβξ : β < ξ := lt_of_lt_of_le hβ htop
  obtain ⟨b, hb⟩ := Ordinal.typein_surj (α := ξ.ToType) (· < ·)
    (show β < Ordinal.type (α := ξ.ToType) (· < ·) by simpa using hβξ)
  have hbl : ∀ c ∈ l, b < c := by
    cases l with
    | nil => simp
    | cons a l =>
      have hba : b < a := (Ordinal.typein_lt_typein (α := ξ.ToType) (· < ·)).mp
        (by simpa only [walkerOrdinalHeight, hb] using hβ)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hba
      · exact lt_trans hba (List.rel_of_pairwise_cons hl hc)
  let t : WalkerOrdinalNode ξ := ⟨b :: l, List.Pairwise.cons hbl hl⟩
  exact ⟨t, rfl, hb⟩

end LogicLineages.ModelsAlgebra.PGroups
