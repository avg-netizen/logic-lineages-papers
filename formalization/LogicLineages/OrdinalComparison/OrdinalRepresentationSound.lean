module
public import LogicLineages.OrdinalComparison.EpsilonZeroCalibration
public import Mathlib.SetTheory.Ordinal.Principal

@[expose] public section

/-! The sound direction of the actual-ordinal representation supplier. Every
finite hereditary notation denotes an ordinal below the calibrated least fixed
point, even before normality is imposed. Surjectivity is a separate obligation.
-/

namespace LogicLineages.OrdinalComparison

theorem zero_lt_epsilonZero : (0 : Ordinal) < epsilonZero := by
  change (0 : Ordinal) < Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 0
  apply Ordinal.lt_nfp_iff.mpr
  exact ⟨1, by simp⟩

theorem epsilonZero_add_principal : Ordinal.IsPrincipal (· + ·) epsilonZero := by
  simpa only [epsilonZeroCalibration.1] using
    Ordinal.isPrincipal_add_omega0_opow epsilonZero

theorem rawNotation_repr_lt_epsilonZero (a : ONote) : a.repr < epsilonZero := by
  induction a with
  | zero => exact zero_lt_epsilonZero
  | oadd e c t ihe iht =>
      have he : Ordinal.omega0 ^ e.repr < epsilonZero :=
        (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ihe
      exact epsilonZero_add_principal
        (epsilonZero_add_principal.mul_natCast_lt he (c : Nat)) iht

theorem normalRepresentationSound : Targets.NormalRepresentationSound :=
  fun a => rawNotation_repr_lt_epsilonZero a.1

end LogicLineages.OrdinalComparison
