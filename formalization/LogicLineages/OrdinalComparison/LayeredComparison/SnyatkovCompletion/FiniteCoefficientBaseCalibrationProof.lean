module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProof
open FiniteCoefficientBase Source Source.ForwardTranslation CommonLayerSyntax

theorem coefficient_calibration (c : ClosedPositive) : Code.coefficient (closedPositiveCode c) = coefficient c := by
  induction c with
  | one => simp [Code.coefficient, closedPositiveCode, coefficient]
  | omega => simp [Code.coefficient, closedPositiveCode, coefficient]
  | add a b iha ihb =>
    rw [closedPositiveCode, Code.coefficient]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, iha, ihb, coefficient]
  | emul a b iha ihb =>
    rw [closedPositiveCode, Code.coefficient]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, iha, ihb, coefficient]

theorem iterate_calibration (k : Nat) (t : BaseTerm) : Code.iterate k t.encode = (iteratePhi k t).encode := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Code.iterate, Nat.rec_add_one, iteratePhi, BaseTerm.encode] using congrArg (fun n => 4*n+3) ih

theorem expand_calibration (k : Nat) (t : BaseTerm) : Code.expand k t.encode = (expand k t).encode := by
  unfold Code.expand expand
  rw [show 4 * Nat.pair t.encode (4 * (2*k)) + 2 = (BaseTerm.add t (.numeral (2*k))).encode from rfl,
    iterate_calibration]
  rfl

theorem scalar_calibration (ι : Type) (index : ι → Nat) (s : Scalar ι) :
    Code.compile (scalarSyntaxCode index s) = (compile index s).map BaseTerm.encode := by
  induction s with
  | one => simp [Code.compile, scalarSyntaxCode, compile, BaseTerm.encode]
  | var i =>
    rw [scalarSyntaxCode, Code.compile]
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.add_div, compile, BaseTerm.encode]
  | add a b iha ihb =>
    rw [scalarSyntaxCode, Code.compile]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
    have hd : (4 * Nat.pair (scalarSyntaxCode index a) (scalarSyntaxCode index b) + 2) / 4 =
      Nat.pair (scalarSyntaxCode index a) (scalarSyntaxCode index b) := by omega
    rw [hd]
    simp only [Nat.unpair_pair]
    rw [iha, ihb]
    cases ha : compile index a <;> cases hb : compile index b <;> simp [compile, ha, hb, BaseTerm.encode]
  | shift c a ih =>
    rw [scalarSyntaxCode, Code.compile]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
    have hd : (4 * Nat.pair (closedPositiveCode c) (scalarSyntaxCode index a) + 3) / 4 =
      Nat.pair (closedPositiveCode c) (scalarSyntaxCode index a) := by omega
    rw [hd]
    simp only [Nat.unpair_pair]
    rw [coefficient_calibration, ih]
    cases hc : coefficient c <;> cases ha : compile index a <;> simp [compile, hc, ha, expand_calibration]

theorem literalNumericCalibration : FiniteCoefficientBaseTargets.LiteralNumericCalibration :=
  ⟨coefficient_calibration, expand_calibration, scalar_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBaseProof
