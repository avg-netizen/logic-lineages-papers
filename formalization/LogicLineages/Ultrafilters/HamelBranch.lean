module

public import LogicLineages.Ultrafilters.HamelBranchTargets
public import LogicLineages.Ultrafilters.HamelLength
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.Ultrafilters

theorem supportDecay_pos {ι : Type*} (B : Module.Basis ι ℚ ℝ) (x : ℝ) :
    0 < supportDecay B x :=
  pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _

theorem supportDecay_le_one {ι : Type*} (B : Module.Basis ι ℚ ℝ) (x : ℝ) :
    supportDecay B x ≤ 1 :=
  pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem vanishing_coordinate_witness : Targets.VanishingCoordinateWitness := by
  intro ι B p hp hz
  have hlength := hamel_length_escapes B p hp hz
  refine ⟨fun x => ⟨supportDecay_pos B x, supportDecay_le_one B x⟩, ?_, ?_⟩
  · intro η hη
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
    apply Filter.mem_of_superset (hlength.2 n)
    intro x hx
    have hpow : supportDecay B x ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_of_lt hx)
    exact hpow.trans_lt hn
  · intro T hT x hx δ hδ
    obtain ⟨y, ⟨⟨hyT, hyδ⟩, hyK⟩, hyLength⟩ := Filter.nonempty_of_mem
      (Filter.inter_mem
        (Filter.inter_mem (Filter.inter_mem hx.2 (hp.2 δ hδ))
          (coordinateKernel_mem B p hz x)) (hlength.2 1))
    refine ⟨y, hyT, hyδ, ?_⟩
    have hpow : (1 / 2 : ℝ) ^ supportLength B y ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_of_lt hyLength)
    have hbound := mul_le_mul_of_nonneg_left hpow (supportDecay_pos B x).le
    change (1 / 2 : ℝ) ^ supportLength B (x + y) < supportDecay B x / 2
    rw [supportLength_add_of_kernel B x y hyK, pow_add]
    change supportDecay B x * (1 / 2 : ℝ) ^ supportLength B y < supportDecay B x / 2
    norm_num at hbound
    linarith [supportDecay_pos B x]

end LogicLineages.Ultrafilters
