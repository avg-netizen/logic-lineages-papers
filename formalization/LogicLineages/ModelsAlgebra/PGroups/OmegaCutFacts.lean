module

public import LogicLineages.ModelsAlgebra.PGroups.QuotientFiltration

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups

open Order

universe u v

theorem omegaCut_two_steps_lt {β γ : Ordinal.{v}}
    (hβ : β < Ordinal.omega0 * γ) : β + 2 < Ordinal.omega0 * γ := by
  have hγ : γ ≠ 0 := by
    intro hz
    subst γ
    simpa using hβ
  have hlimit : IsSuccLimit (Ordinal.omega0 * γ) :=
    Ordinal.isSuccLimit_mul_left Ordinal.isSuccLimit_omega0
      (bot_lt_iff_ne_bot.mpr hγ)
  have hnext := hlimit.succ_lt (hlimit.succ_lt hβ)
  simpa only [succ_eq_add_one, add_assoc, one_add_one_eq_two] using hnext

variable {G : Type u} [AddCommGroup G]

theorem transfiniteFiltration_add_two (p : ℕ) (β : Ordinal.{v}) :
    (transfiniteFiltration p (β + 2) : AddSubgroup G) =
      pStep p (pStep p (transfiniteFiltration p β)) := by
  rw [← one_add_one_eq_two, ← add_assoc,
    transfiniteFiltration_add_one, transfiniteFiltration_add_one]

theorem omegaCut_kernel_le_secondStep (p : ℕ) (T : AddSubgroup G)
    (γ : Ordinal.{v}) (hT : T ≤ transfiniteFiltration p (Ordinal.omega0 * γ))
    {β : Ordinal.{v}} (hβ : β < Ordinal.omega0 * γ) :
    (QuotientAddGroup.mk' T).ker ≤
      pStep p (pStep p (transfiniteFiltration p β)) := by
  rw [QuotientAddGroup.ker_mk']
  have hcut : T ≤ (transfiniteFiltration p (β + 2) : AddSubgroup G) :=
    hT.trans (transfiniteFiltration_antitone p (omegaCut_two_steps_lt hβ).le)
  rw [transfiniteFiltration_add_two] at hcut
  exact hcut

end LogicLineages.ModelsAlgebra.PGroups
