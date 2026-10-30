module
public import LogicLineages.ModelsAlgebra.PGroups.BelowCutSelectionTargets
public import LogicLineages.ModelsAlgebra.PGroups.PowerStepSelection
public import LogicLineages.ModelsAlgebra.PGroups.CosetNormalization
public import LogicLineages.ModelsAlgebra.PGroups.ExactHeight
public import Mathlib.Tactic.Abel
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem below_cut_selection : Targets.groupBelowCutSelection.{u,v} := by
  intro G _ p hG B D _ δ hBD hnot hcut
  obtain ⟨y,hyD,hyB,hpy⟩ := power_step_selection G p hG B D hBD hnot
  obtain ⟨b,hb,hpb⟩ := coset_double_maximum.{u,v} G p B y
  let x : G := y+b
  have hxD : x ∈ D := D.add_mem hyD (hBD b.property)
  have hxB : x ∉ B := by
    intro hx
    have hm := B.sub_mem hx b.property
    exact hyB (by simpa only [x,add_sub_cancel_right] using hm)
  have hpx : p • x ∈ B := by
    change p • (y+(b:G)) ∈ B
    rw [smul_add]
    exact B.add_mem hpy (B.nsmul_mem b.property p)
  have hxcut : x ∉ (transfiniteFiltration p δ : AddSubgroup G) :=
    fun hx => hxB (hcut ⟨hxD,hx⟩)
  obtain ⟨α,hαδ,hx,hxnot⟩ := exact_height_below_cut G p δ x hxcut
  have hproper : ∀ (c : B) (β : Ordinal.{v}),
      x+c ∈ (transfiniteFiltration p β : AddSubgroup G) →
      x ∈ (transfiniteFiltration p β : AddSubgroup G) := by
    intro c β hc
    apply hb (b+c) β
    simpa only [x,AddSubgroup.coe_add,add_assoc] using hc
  refine ⟨x,α,hxD,hxB,hpx,hxcut,hαδ,hx,hxnot,hproper,?_⟩
  intro c hc β hpc
  have hcmax : ∀ (d : B) (γ : Ordinal.{v}),
      y+d ∈ (transfiniteFiltration p γ : AddSubgroup G) →
      y+(b+c:B) ∈ (transfiniteFiltration p γ : AddSubgroup G) := by
    intro d γ hd
    have he : x + ((d-b:B):G) = y+(d:G) := by
      change (y+(b:G))+((d:G)-(b:G)) = y+(d:G)
      abel
    have hm : x + ((d-b:B):G) ∈ (transfiniteFiltration p γ : AddSubgroup G) := by
      rw [he]
      exact hd
    have hr := hc (d-b) γ hm
    simpa only [x,AddSubgroup.coe_add,add_assoc] using hr
  exact hpb (b+c) hcmax β (by
    simpa only [x,AddSubgroup.coe_add,add_assoc] using hpc)

end LogicLineages.ModelsAlgebra.PGroups
