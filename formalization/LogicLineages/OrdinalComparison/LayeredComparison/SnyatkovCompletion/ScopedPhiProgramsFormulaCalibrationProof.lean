module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsTermCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionCodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
open ScopedPhiPrograms

theorem test_calibration (names : List Nat) (p : SourceFormula) :
    Code.test names p.encode = ScopedPhiParameters.test names p := by
  induction p generalizing names with
  | equal a b => rw [Code.test]; simp [SourceFormula.encode, ScopedPhiParameters.test, termTest_calibration]
  | less a b => rw [Code.test]; simp [SourceFormula.encode, ScopedPhiParameters.test, Nat.add_mod, Nat.add_div, termTest_calibration]
  | negative p ih => rw [Code.test]; simp [SourceFormula.encode, ScopedPhiParameters.test, Nat.add_mod, Nat.add_div, ih]
  | conjunction p q ihp ihq => rw [Code.test]; simp [SourceFormula.encode, ScopedPhiParameters.test, Nat.add_mod, Nat.add_div, ihp, ihq]
  | existsNat i p ih => rw [Code.test]; simp [SourceFormula.encode, ScopedPhiParameters.test, Nat.add_mod, Nat.add_div, ih]

theorem freezeFormula_calibration (values : List Nat) (p : SourceFormula) :
    Code.freezeFormula values p.encode = (ScopedPhiParameters.freezeFormula (PlainParameterDecision.valuation values) p).encode := by
  induction p with
  | equal a b => rw [Code.freezeFormula]; simp [SourceFormula.encode, ScopedPhiParameters.freezeFormula, freezeTerm_calibration]
  | less a b => rw [Code.freezeFormula]; simp [SourceFormula.encode, ScopedPhiParameters.freezeFormula, Nat.add_mod, Nat.add_div, freezeTerm_calibration]
  | negative p ih => rw [Code.freezeFormula]; simp [SourceFormula.encode, ScopedPhiParameters.freezeFormula, Nat.add_mod, Nat.add_div, ih]
  | conjunction p q ihp ihq => rw [Code.freezeFormula]; simp [SourceFormula.encode, ScopedPhiParameters.freezeFormula, Nat.add_mod, Nat.add_div, ihp, ihq]
  | existsNat i p ih => rw [Code.freezeFormula]; simp [SourceFormula.encode, ScopedPhiParameters.freezeFormula, Nat.add_mod, Nat.add_div, ih]

theorem literalFormulaData : ScopedPhiProgramsTargets.LiteralFormulaData :=
  ⟨test_calibration, freezeFormula_calibration⟩

theorem literalDecision : ScopedPhiProgramsTargets.LiteralDecision := by
  intro values p
  unfold Code.decide ScopedPhiParameters.decide
  rw [test_calibration, freezeFormula_calibration, AdditiveParameterDecisionProof.literalCodeDecision]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
