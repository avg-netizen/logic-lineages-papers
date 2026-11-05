module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsValueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
open CommonLayerSyntax ScopedPhiPrograms

theorem termTest_calibration (names : List Nat) (t : BaseTerm) :
    Code.termTest names t.encode = ScopedPhiParameters.termTest names t := by
  induction t with
  | numeral n => rw [Code.termTest]; simp [BaseTerm.encode, ScopedPhiParameters.termTest]
  | «variable» i => rw [Code.termTest]; simp [BaseTerm.encode, ScopedPhiParameters.termTest, Nat.add_mod]
  | add a b iha ihb =>
      rw [Code.termTest]
      simp [BaseTerm.encode, ScopedPhiParameters.termTest, Nat.add_mod, Nat.add_div, Nat.unpair_pair, iha, ihb]
  | phi t ih =>
      rw [Code.termTest]
      simp [BaseTerm.encode, ScopedPhiParameters.termTest, Nat.add_mod, Nat.add_div,
        BaseTermPrograms.variablesCode]
      rw [CommonLayerSyntax.Proof.baseRoundtrip t]

theorem freezeTerm_calibration (values : List Nat) (t : BaseTerm) :
    Code.freezeTerm values t.encode = (ScopedPhiParameters.freezeTerm (PlainParameterDecision.valuation values) t).encode := by
  induction t with
  | numeral n => rw [Code.freezeTerm]; simp [BaseTerm.encode, ScopedPhiParameters.freezeTerm]
  | «variable» i => rw [Code.freezeTerm]; simp [BaseTerm.encode, ScopedPhiParameters.freezeTerm, Nat.add_mod]
  | add a b iha ihb =>
      rw [Code.freezeTerm]
      simp [BaseTerm.encode, ScopedPhiParameters.freezeTerm, Nat.add_mod, Nat.add_div, Nat.unpair_pair, iha, ihb]
  | phi t ih =>
      have hv := actualZeroDefaultEvaluation values (.phi t)
      rw [Code.freezeTerm]
      simpa [BaseTerm.encode, ScopedPhiParameters.freezeTerm, Nat.add_mod, Nat.add_div] using hv

theorem literalTermData : ScopedPhiProgramsTargets.LiteralTermData :=
  ⟨termTest_calibration, freezeTerm_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
