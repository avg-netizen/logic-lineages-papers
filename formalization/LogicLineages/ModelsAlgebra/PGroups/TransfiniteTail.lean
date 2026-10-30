module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem transfinite_tail_membership : Targets.groupTransfiniteTailMembership := by
  intro G _ p δ β
  refine Ordinal.limitRecOn β ?_ (fun γ ih => ?_) (fun γ hγ ih => ?_)
  · intro x
    rw [add_zero, transfiniteFiltration_zero]
    exact ⟨fun _ => x.property, fun _ => AddSubgroup.mem_top _⟩
  · intro x
    rw [transfiniteFiltration_add_one, ← add_assoc, transfiniteFiltration_add_one]
    constructor
    · rintro ⟨y,hy,he⟩
      exact ⟨(y:G), (ih y).mp hy, congrArg Subtype.val he⟩
    · rintro ⟨y,hy,he⟩
      have hyδ : y ∈ (transfiniteFiltration p δ : AddSubgroup G) :=
        transfiniteFiltration_antitone p le_self_add hy
      refine ⟨⟨y,hyδ⟩, (ih ⟨y,hyδ⟩).mpr hy, ?_⟩
      exact Subtype.ext he
  · intro x
    rw [transfiniteFiltration_limit p hγ,
      transfiniteFiltration_limit p (Ordinal.isSuccLimit_add δ hγ)]
    constructor
    · intro hx
      apply AddSubgroup.mem_iInf.mpr
      intro ξ
      obtain ⟨η,hηγ,hξη⟩ := Ordinal.lt_add_iff hγ.ne_bot |>.mp ξ.property
      have hxη := (ih η hηγ x).mp (AddSubgroup.mem_iInf.mp hx ⟨η,hηγ⟩)
      exact transfiniteFiltration_antitone p hξη hxη
    · intro hx
      apply AddSubgroup.mem_iInf.mpr
      intro η
      apply (ih η.val η.property x).mpr
      exact AddSubgroup.mem_iInf.mp hx ⟨δ+η.val, (add_lt_add_iff_left δ).mpr η.property⟩

theorem transfinite_tail_image : Targets.groupTransfiniteTailImage := by
  intro G _ p δ β
  apply AddSubgroup.ext
  intro x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (transfinite_tail_membership G p δ β y).mp hy
  · intro hx
    have hxδ : x ∈ (transfiniteFiltration p δ : AddSubgroup G) :=
      transfiniteFiltration_antitone p le_self_add hx
    exact ⟨⟨x,hxδ⟩, (transfinite_tail_membership G p δ β ⟨x,hxδ⟩).mpr hx, rfl⟩

end LogicLineages.ModelsAlgebra.PGroups
