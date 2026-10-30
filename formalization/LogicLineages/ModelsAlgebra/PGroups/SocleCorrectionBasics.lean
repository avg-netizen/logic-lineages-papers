module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionBasicsTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem socle_correction_representative : Targets.groupSocleCorrectionRepresentative.{u} := by
  intro G _ p S x hx hpx
  obtain ⟨y,hy,he⟩ := hpx
  change p • y = p • x at he
  refine ⟨y,hy,he,S.sub_mem hx (pStep_le p S hy),?_⟩
  change p • (x-y) = 0
  rw [smul_sub,he,sub_self]

theorem socle_correction_equality : Targets.groupSocleCorrectionEquality.{u} := by
  intro G _ p S a b
  change ((a : UlmLayer p S) = (b : UlmLayer p S)) ↔ (a:G)-b ∈ pStep p S
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change ((a:G)-b ∈ pStep p S ∧ p • ((a:G)-b) = 0) ↔ (a:G)-b ∈ pStep p S
  have ha : p • (a:G) = 0 := a.property.2
  have hb : p • (b:G) = 0 := b.property.2
  simp only [smul_sub,ha,hb,sub_self,and_true]

end LogicLineages.ModelsAlgebra.PGroups
