module
public import LogicLineages.OrdinalComparison.WWSourcePositivePolynomialTargets
public import LogicLineages.OrdinalComparison.WWSourcePolynomialArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open ForwardTranslation

private theorem omega_lt_square : Ordinal.omega0 < Ordinal.omega0 ^ (2 : Ordinal) := by
  have h := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    (show (1 : Ordinal) < 2 by exact_mod_cast (show (1 : Nat) < 2 by omega))
  simpa only [Ordinal.opow_one] using h

private theorem omega_lt_polynomial : Ordinal.omega0 < Ordinal.omega0 ^ Ordinal.omega0 := by
  simpa only [Ordinal.opow_one] using
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr Ordinal.one_lt_omega0

theorem positiveHeightZeroLinearBound : Targets.PositiveHeightZeroLinearBound := by
  intro c hc
  induction c with
  | one =>
    simpa [ClosedPositive.evaluate, ONote.repr] using Ordinal.one_lt_omega0.trans omega_lt_square
  | omega => simpa [ClosedPositive.evaluate, ONote.repr] using omega_lt_square
  | add a b iha ihb =>
    have hp : positiveHeadHeight a = 0 ∧ positiveHeadHeight b = 0 := by
      simp only [positiveHeadHeight] at hc
      omega
    change (naturalSum a.evaluate b.evaluate).1.repr < _
    rw [naturalSumDenotation]
    exact sourceNaturalSumPowerClosure _ _ _ (normalRepresentationSound a.evaluate)
      (normalRepresentationSound b.evaluate) (iha hp.1) (ihb hp.2)
  | emul a b iha ihb => simp only [positiveHeadHeight] at hc; omega

private theorem power_repr (a : ClosedPositive) :
    (NONote.opow ⟨ONote.ofNat 2, ONote.nf_ofNat 2⟩ a.evaluate).1.repr =
      (2 : Ordinal) ^ a.evaluate.1.repr := by
  change ((ONote.ofNat 2) ^ a.evaluate.1).repr = _
  letI : ONote.NF a.evaluate.1 := a.evaluate.2
  rw [ONote.repr_opow, ONote.repr_ofNat]
  rfl

theorem positiveHeightOnePolynomialBound : Targets.PositiveHeightOnePolynomialBound := by
  intro c hc
  induction c with
  | one =>
    simpa [ClosedPositive.evaluate, ONote.repr] using Ordinal.one_lt_omega0.trans omega_lt_polynomial
  | omega => simpa [ClosedPositive.evaluate, ONote.repr] using omega_lt_polynomial
  | add a b iha ihb =>
    have hp : positiveHeadHeight a ≤ 1 ∧ positiveHeadHeight b ≤ 1 := Nat.max_le.mp hc
    change (naturalSum a.evaluate b.evaluate).1.repr < _
    rw [naturalSumDenotation]
    exact sourceNaturalSumPowerClosure _ _ _ (normalRepresentationSound a.evaluate)
      (normalRepresentationSound b.evaluate) (iha hp.1) (ihb hp.2)
  | emul a b iha ihb =>
    have hp : positiveHeadHeight a = 0 ∧ positiveHeadHeight b ≤ 1 := by
      simp only [positiveHeadHeight] at hc
      omega
    change (naturalProduct (NONote.opow ⟨ONote.ofNat 2, _⟩ a.evaluate) b.evaluate).1.repr < _
    rw [naturalProductDenotation, power_repr]
    exact sourceNaturalProductPolynomialClosure _ _
      (sourceBaseTwoLinearPolynomial _ (positiveHeightZeroLinearBound a hp.1)) (ihb hp.2)
end LogicLineages.OrdinalComparison.Source.SourceClasses
