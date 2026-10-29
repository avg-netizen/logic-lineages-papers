module

public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteFiltration
public import LogicLineages.ModelsAlgebra.PGroups.ImageIntersections

@[expose] public section

/-!
# Ordinal filtration and images below a kernel cut

This proves the source's actual transfinite induction. At limit stages
kernel containment is derived from the one cut hypothesis and proved
antitonicity, then the accepted saturated-intersection identity applies.
No filtration/image property is supplied as a premise.
-/

namespace LogicLineages.ModelsAlgebra.PGroups

open Order

universe u v w

variable {G : Type u} [AddCommGroup G]

@[simp] theorem transfiniteFiltration_zero (p : ℕ) :
    (transfiniteFiltration p (0 : Ordinal.{v}) : AddSubgroup G) = ⊤ :=
  Ordinal.limitRecOn_zero _ _ _

theorem transfiniteFiltration_add_one (p : ℕ) (α : Ordinal.{v}) :
    (transfiniteFiltration p (α + 1) : AddSubgroup G) =
      pStep p (transfiniteFiltration p α) :=
  Ordinal.limitRecOn_add_one α _ _ _

theorem transfiniteFiltration_limit (p : ℕ) {α : Ordinal.{v}} (hα : IsSuccLimit α) :
    (transfiniteFiltration p α : AddSubgroup G) =
      ⨅ β : Set.Iio α, transfiniteFiltration p β.1 :=
  Ordinal.limitRecOn_limit α _ _ _ hα

theorem pStep_le (p : ℕ) (S : AddSubgroup G) : pStep p S ≤ S := by
  rintro x ⟨y, hy, rfl⟩
  exact S.nsmul_mem hy p

theorem transfiniteFiltration_antitone (p : ℕ) :
    Antitone (fun α : Ordinal.{v} => (transfiniteFiltration p α : AddSubgroup G)) := by
  have hdesc : ∀ β : Ordinal.{v}, ∀ α ≤ β,
      (transfiniteFiltration p β : AddSubgroup G) ≤ transfiniteFiltration p α := by
    intro β
    refine Ordinal.limitRecOn β ?_ (fun γ ih => ?_) (fun γ hγ ih => ?_)
    · intro α hα
      have hzero : α = 0 := le_antisymm hα bot_le
      subst α
      exact le_rfl
    · intro α hα
      rcases lt_or_eq_of_le hα with hlt | rfl
      · rw [transfiniteFiltration_add_one]
        exact (pStep_le p _).trans (ih α (lt_add_one_iff.mp hlt))
      · exact le_rfl
    · intro α hα
      rcases lt_or_eq_of_le hα with hlt | rfl
      · rw [transfiniteFiltration_limit p hγ]
        exact iInf_le
          (fun β : Set.Iio γ => (transfiniteFiltration p β.1 : AddSubgroup G)) ⟨α, hlt⟩
      · exact le_rfl
  intro α β hαβ
  exact hdesc β α hαβ

variable {H : Type w} [AddCommGroup H]

theorem map_transfiniteFiltration_below (p : ℕ) (f : G →+ H)
    (hf : Function.Surjective f) (δ : Ordinal.{v})
    (hker : f.ker ≤ transfiniteFiltration p δ) :
    ∀ α ≤ δ, (transfiniteFiltration p α : AddSubgroup G).map f =
      (transfiniteFiltration p α : AddSubgroup H) := by
  intro α
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · intro _
    rw [transfiniteFiltration_zero, transfiniteFiltration_zero]
    exact AddSubgroup.map_top_of_surjective f hf
  · intro hβδ
    have hpre : β ≤ δ :=
      (le_of_lt (lt_add_one_iff.mpr le_rfl)).trans hβδ
    rw [transfiniteFiltration_add_one (G := G),
      transfiniteFiltration_add_one (G := H), map_pStep, ih hpre]
  · intro hβδ
    have hk : ∀ γ : Set.Iio β, f.ker ≤ (transfiniteFiltration p γ.1 : AddSubgroup G) :=
      fun γ => hker.trans (transfiniteFiltration_antitone p ((le_of_lt γ.2).trans hβδ))
    rw [transfiniteFiltration_limit (G := G) p hβ,
      transfiniteFiltration_limit (G := H) p hβ,
      map_iInf_of_ker_le f hf _ hk]
    congr 1
    funext γ
    exact ih γ.1 γ.2 ((le_of_lt γ.2).trans hβδ)

end LogicLineages.ModelsAlgebra.PGroups
