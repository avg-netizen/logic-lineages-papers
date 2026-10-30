module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteFullFiltrationExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.FiniteBelowLimitExtension
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem finite_full_filtration_extension : Targets.groupFiniteFullFiltrationExtension.{u,v} := by
  classical
  intro G H _ _ p _ hG hH D _ B C f δ hδ hBD hcut hpres hRank
  obtain ⟨F,hF,hFa,hFp⟩ := finite_below_limit_extension G H p hG hH D B C f δ hδ
    hBD hcut (fun b β _ => hpres b β) hRank
  refine ⟨F,hF,hFa,?_⟩
  intro y β
  by_cases hβ : β ≤ δ
  · exact hFp y β hβ
  · have hδβ : δ ≤ β := le_of_lt (lt_of_not_ge hβ)
    have hagree (hyB : (y:G) ∈ B) : F y = (f ⟨y,hyB⟩:H) := hFa ⟨y,hyB⟩
    constructor
    · intro hy
      have hyδ : F y ∈ (transfiniteFiltration p δ : AddSubgroup H) :=
        transfiniteFiltration_antitone p hδβ hy
      have hyGδ := (hFp y δ le_rfl).mp hyδ
      have hyB : (y:G) ∈ B := hcut ⟨y.property,hyGδ⟩
      rw [hagree hyB] at hy
      exact (hpres ⟨y,hyB⟩ β).mp hy
    · intro hy
      have hyδ : (y:G) ∈ (transfiniteFiltration p δ : AddSubgroup G) :=
        transfiniteFiltration_antitone p hδβ hy
      have hyB : (y:G) ∈ B := hcut ⟨y.property,hyδ⟩
      rw [hagree hyB]
      exact (hpres ⟨y,hyB⟩ β).mpr hy

end LogicLineages.ModelsAlgebra.PGroups
