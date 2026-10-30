module
public import LogicLineages.OrdinalComparison.CartierSupportTargets
public import LogicLineages.OrdinalComparison.CartierLaurentProof
public import Mathlib.Tactic.Linarith

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualDifferentialCartierIteratedCoefficient :
    Targets.ActualDifferentialCartierIteratedCoefficient.{u} := by
  intro K _ _ _ z f j n
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', actualDifferentialCartierLaurentCoefficient, ih]
    have hi : (2 : Int) ^ j * ((2 * n + 1) + 1) - 1 =
        (2 : Int) ^ (j + 1) * (n + 1) - 1 := by rw [pow_succ]; ring
    rw [hi]
    rw [show j + 1 = 1 + j by omega, iterateFrobeniusEquiv_symm_add_apply,
      iterateFrobeniusEquiv_one]

theorem actualDifferentialCartierSupportContraction :
    Targets.ActualDifferentialCartierSupportContraction.{u} := by
  intro K _ _ _ z f μ a hf hμ n hn
  have hμ' : (μ : Int) ≤ (2 : Int) ^ a := by exact_mod_cast hμ
  have hp : 0 < (2 : Int) ^ a := pow_pos (by decide) _
  have hi : (2 : Int) ^ a * (n + 1) - 1 < -(μ : Int) := by nlinarith
  rw [actualDifferentialCartierIteratedCoefficient, hf _ hi, map_zero]

end LogicLineages.OrdinalComparison
