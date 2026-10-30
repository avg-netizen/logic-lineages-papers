module

public import LogicLineages.ModelsAlgebra.PGroups.ShiftLimitTargets
public import LogicLineages.ModelsAlgebra.PGroups.ShiftGroup
public import LogicLineages.ModelsAlgebra.PGroups.LimitRoots
public import LogicLineages.ModelsAlgebra.PGroups.LimitPiTwo

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe v

theorem shift_exponent : Targets.groupShiftExponent := by
  intro p _ x
  apply Prod.ext
  · have hu (u : ZMod p) : p ^ 2 • u = 0 := by
      rw [pow_two, mul_nsmul, ZModModule.char_nsmul_eq_zero p u, nsmul_zero]
    exact hu x.1
  · apply Finsupp.ext
    intro i
    exact ZModModule.char_nsmul_eq_zero (p ^ 2) (x.2 i)

theorem shift_limit_socle_roots : Targets.groupShiftLimitSocleRoots := by
  intro p _
  exact limit_socle_roots (ShiftGroup p) (shiftHom p) (shift_injective p) p p
    (shift_socle_roots p)

theorem shift_limit_not_isomorphic : Targets.groupShiftLimitNotIsomorphic := by
  intro p _ he
  obtain ⟨e⟩ := he
  have hx : p • e ((1, 0) : ShiftGroup p) = 0 := by
    simpa only [map_nsmul, map_zero] using congrArg e (shift_short_no_root p).1
  obtain ⟨y, hy⟩ := shift_limit_socle_roots p _ hx
  apply (shift_short_no_root p).2
  refine ⟨e.symm y, ?_⟩
  apply e.injective
  simpa only [map_nsmul, e.apply_symm_apply] using hy

theorem shift_no_pi_two_scott : Targets.groupShiftNoPiTwoScott.{v} := by
  intro p _ φ hφ hs
  letI : Countable (ShiftGroup p) := shift_countable p
  letI : Countable (EndomorphismLimit (shiftHom p)) :=
    endomorphism_limit_countable (ShiftGroup p) (shiftHom p)
  apply shift_limit_not_isomorphic p
  exact hs.2 (EndomorphismLimit (shiftHom p))
    (endomorphism_limit_pi_two (ShiftGroup p) (shiftHom p) (shift_injective p) φ hφ hs.1)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
