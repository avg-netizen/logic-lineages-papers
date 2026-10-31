module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiltrationTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerSupportProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open Order

private theorem height_span_zero (p : ℕ) (hp : 0 < p) (ξ : Ordinal.{0})
    [Countable ξ.ToType] : walkerHeightSpan p ξ 0 = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨d, hd, _⟩ := walker_source_unique_digits p hp ξ x
  rw [← hd.2]
  exact (walker_source_height_support p hp ξ 0 d hd.1).mpr (fun _ _ => bot_le)

private theorem height_span_successor (p : ℕ) (ξ α : Ordinal.{0}) :
    pStep p (walkerHeightSpan p ξ α) = walkerHeightSpan p ξ (α+1) := by
  let gen := walkerPresentedGenerator p (walkerOrdinalParent ξ)
  apply le_antisymm
  · have hpre : walkerHeightSpan p ξ α ≤
        (walkerHeightSpan p ξ (α+1)).comap (nsmulAddMonoidHom p) := by
      apply (AddSubgroup.closure_le _).mpr
      rintro _ ⟨s, hs, rfl⟩
      change p • gen s ∈ walkerHeightSpan p ξ (α+1)
      rw [walker_presented_relations (WalkerOrdinalNode ξ) p (walkerOrdinalParent ξ) s]
      cases h : walkerOrdinalParent ξ s with
      | none => simpa [h] using (walkerHeightSpan p ξ (α+1)).zero_mem
      | some t =>
        have ht : α+1 ≤ walkerOrdinalHeight ξ t :=
          add_one_le_iff.mpr (lt_of_le_of_lt hs (walker_ordinal_parent_height ξ s t h))
        simp only [h, Option.elim_some]
        exact AddSubgroup.subset_closure ⟨t, ht, rfl⟩
    rintro x ⟨y, hy, rfl⟩
    exact hpre hy
  · apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hheight⟩ := walker_ordinal_children ξ s α (add_one_le_iff.mp hs)
    refine ⟨gen t, AddSubgroup.subset_closure ⟨t, hheight.ge, rfl⟩, ?_⟩
    change p • gen t = gen s
    simpa [ht] using walker_presented_relations (WalkerOrdinalNode ξ) p (walkerOrdinalParent ξ) t

private theorem height_span_limit (p : ℕ) (hp : 0 < p) (ξ α : Ordinal.{0})
    [Countable ξ.ToType] (hα : IsSuccLimit α) :
    (⨅ β : Set.Iio α, walkerHeightSpan p ξ β.val) = walkerHeightSpan p ξ α := by
  apply AddSubgroup.ext
  intro x
  obtain ⟨d, hd, _⟩ := walker_source_unique_digits p hp ξ x
  rw [← hd.2]
  simp only [AddSubgroup.mem_iInf]
  rw [walker_source_height_support p hp ξ α d hd.1]
  constructor
  · intro h s hs
    apply hα.le_iff_forall_le.mpr
    intro β hβ
    exact (walker_source_height_support p hp ξ β d hd.1).mp (h ⟨β,hβ⟩) s hs
  · intro h β
    apply (walker_source_height_support p hp ξ β.val d hd.1).mpr
    intro s hs
    exact β.property.le.trans (h s hs)

theorem walker_source_filtration : Targets.walkerSourceFiltration := by
  intro p hp ξ _ α
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · rw [transfiniteFiltration_zero]
    exact (height_span_zero p hp ξ).symm
  · rw [transfiniteFiltration_add_one, ih]
    exact height_span_successor p ξ β
  · rw [transfiniteFiltration_limit p hβ]
    calc
      (⨅ γ : Set.Iio β, (transfiniteFiltration p γ.val : AddSubgroup (WalkerSourceGroup p ξ))) =
          ⨅ γ : Set.Iio β, walkerHeightSpan p ξ γ.val := iInf_congr (fun γ => ih γ.val γ.property)
      _ = walkerHeightSpan p ξ β := height_span_limit p hp ξ β hβ

end LogicLineages.ModelsAlgebra.PGroups
