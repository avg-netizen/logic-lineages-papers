module
public import LogicLineages.ModelsAlgebra.PGroups.SuccessorRootTargets
public import LogicLineages.ModelsAlgebra.PGroups.ProperRepresentative
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem successor_suitable_root : Targets.groupSuccessorSuitableRoot.{u,v} := by
  intro G H _ _ p _ B x α hxB hpx f hf hpres hx hxnot hpx1 hpxnot hproper hmax
  let px : B := ⟨p • x,hpx⟩
  have hα : α ≤ α + 1 := le_self_add
  have hα2 : α ≤ α + 1 + 1 := hα.trans le_self_add
  have hy1 : f px ∈ (transfiniteFiltration p (α+1) : AddSubgroup H) :=
    (hpres px (α+1) le_self_add).mpr hpx1
  rw [transfiniteFiltration_add_one] at hy1
  obtain ⟨w,hwα,hw⟩ := hy1
  change p • w = f px at hw
  have hw_not : w ∉ (transfiniteFiltration p (α+1) : AddSubgroup H) := by
    intro hw1
    have hpw2 : p • w ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup H) := by
      rw [transfiniteFiltration_add_one]
      exact ⟨w,hw1,rfl⟩
    rw [hw] at hpw2
    exact hpxnot ((hpres px (α+1+1) le_rfl).mp hpw2)
  have hbad (b : B) : w + f b ∉ (transfiniteFiltration p (α+1) : AddSubgroup H) := by
    intro hwb
    have hfb : f b ∈ (transfiniteFiltration p α : AddSubgroup H) := by
      have hm := (transfiniteFiltration p α : AddSubgroup H).sub_mem
        (transfiniteFiltration_antitone p hα hwb) hwα
      simpa only [add_sub_cancel_left] using hm
    have hb : (b:G) ∈ (transfiniteFiltration p α : AddSubgroup G) :=
      (hpres b α hα2).mp hfb
    have hxb := (transfiniteFiltration p α : AddSubgroup G).add_mem hx hb
    have hrep := proper_representative G p B x α hx hxnot hproper b hxb
    let c : B := px + p • b
    have hfc : f c = p • (w + f b) := by
      change f (px + p • b) = p • (w + f b)
      rw [map_add, map_nsmul, ← hw, smul_add]
    have hfc2 : f c ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup H) := by
      rw [hfc, transfiniteFiltration_add_one]
      exact ⟨w+f b,hwb,rfl⟩
    have hc2 := (hpres c (α+1+1) le_rfl).mp hfc2
    change p • x + p • (b:G) ∈ (transfiniteFiltration p (α+1+1) : AddSubgroup G) at hc2
    rw [← smul_add] at hc2
    exact hpxnot (hmax b hrep (α+1+1) hc2)
  have hwrange : w ∉ f.range := by
    rintro ⟨b,hb⟩
    apply hbad (-b)
    simp only [map_neg, hb, add_neg_cancel]
    exact (transfiniteFiltration p (α+1) : AddSubgroup H).zero_mem
  refine ⟨w,hw,hwα,hw_not,hwrange,?_⟩
  intro b β hwb
  by_cases hβα : β ≤ α
  · exact transfiniteFiltration_antitone p hβα hwα
  · have hαβ : α + 1 ≤ β := Order.succ_le_of_lt (lt_of_not_ge hβα)
    exact False.elim (hbad b (transfiniteFiltration_antitone p hαβ hwb))

end LogicLineages.ModelsAlgebra.PGroups
