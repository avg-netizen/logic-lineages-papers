module
public import LogicLineages.ModelsAlgebra.PGroups.SoclePullbackTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- The correction to a chosen p-root lies in the previous-stage socle.
Surjectivity onto that socle is exactly what keeps the pullback kernel in
all stages through the prescribed cut. -/
theorem actual_socle_pullback_filtration : Targets.actualSoclePullbackFiltration := by
  classical
  intro p B C E _ _ _ f q δ hp hq hd hs
  constructor
  · intro b
    obtain ⟨e,he⟩ := hq (f b)
    exact ⟨⟨(b,e),he.symm⟩,rfl⟩
  · intro α
    refine Ordinal.limitRecOn α ?_ (fun β ih=>?_) (fun β hβ ih=>?_)
    · intro _ x
      simp only [transfiniteFiltration_zero,AddSubgroup.mem_top]
    · intro hα x
      have hpre : β≤δ := (Order.lt_add_one_iff.mpr le_rfl).le.trans hα
      have hβδ : β<δ := lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) hα
      rw [transfiniteFiltration_add_one,transfiniteFiltration_add_one]
      constructor
      · rintro ⟨y,hy,hxy⟩
        refine ⟨y.val.1,(ih hpre y).mp hy,?_⟩
        exact congrArg (fun z:HomPullback f q=>z.val.1) hxy
      · rintro ⟨b,hb,hpb⟩
        change p • b=x.val.1 at hpb
        obtain ⟨e,he⟩ := hd p hp x.val.2
        let c : C := f b-q e
        have hc : p • c=0 := by
          change p • (f b-q e)=0
          rw [nsmul_sub,←map_nsmul,←map_nsmul,hpb,he]
          exact sub_eq_zero.mpr x.property
        obtain ⟨z,hz⟩ := hs β hβδ ⟨c,⟨AddSubgroup.mem_top _,hc⟩⟩
        let y : HomPullback f q := ⟨(b-(z:B),e),by
          change f (b-(z:B))=q e
          rw [map_sub,hz]
          change f b-(f b-q e)=q e
          abel⟩
        have hy : y∈(transfiniteFiltration p β:AddSubgroup (HomPullback f q)) := by
          apply (ih hpre y).mpr
          exact (transfiniteFiltration p β:AddSubgroup B).sub_mem hb z.property.1
        refine ⟨y,hy,?_⟩
        apply Subtype.ext
        apply Prod.ext
        · change p • (b-(z:B))=x.val.1
          have hz0 : p • (z:B)=0 := z.property.2
          rw [nsmul_sub,hz0,sub_zero,hpb]
        · exact he
    · intro hα x
      rw [transfiniteFiltration_limit p hβ,transfiniteFiltration_limit p hβ]
      simp only [AddSubgroup.mem_iInf]
      constructor
      · intro hx η
        exact (ih η.val η.property (η.property.le.trans hα) x).mp (hx η)
      · intro hx η
        exact (ih η.val η.property (η.property.le.trans hα) x).mpr (hx η)
end LogicLineages.ModelsAlgebra.PGroups
