module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsValueProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecRoundtripProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsProof
open CommonLayerSyntax BoundedSourcePrograms

theorem exactFiniteUpdate : BoundedSourceProgramsTargets.ExactFiniteUpdate := by
  intro values i n j
  by_cases hj : j < max values.length (i + 1)
  · simp only [PlainParameterDecision.valuation, Code.update, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
    by_cases hji : j = i
    · subst j; simp
    · simp [hji, Function.update_of_ne hji, PlainParameterDecision.valuation, List.getD_eq_getElem?_getD]
  · have hu : (Code.update values i n).length ≤ j := by simp only [Code.update, List.length_map, List.length_range]; omega
    have hv : values.length ≤ j := by omega
    have hji : j ≠ i := by omega
    rw [PlainParameterDecision.valuation, List.getD_eq_default _ _ hu, Function.update_of_ne hji]
    exact (List.getD_eq_default values 0 hv).symm

theorem variables_calibration (t : BaseTerm) : BaseTermPrograms.variablesCode t.encode = t.variables := by
  unfold BaseTermPrograms.variablesCode
  rw [CommonLayerSyntax.Proof.baseRoundtrip t]

theorem literalGuardCode : BoundedSourceProgramsTargets.LiteralGuardCode := by
  intro i p
  cases p with
  | equal a b => simp [Code.guard, SourceFormula.encode, BoundedSource.guard]
  | less a b => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod]
  | negative p => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod]
  | existsNat j p => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod]
  | conjunction a b =>
      cases a with
      | equal c d => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod, Nat.add_div]
      | negative p => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod, Nat.add_div]
      | conjunction c d => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod, Nat.add_div]
      | existsNat j p => simp [Code.guard, SourceFormula.encode, BoundedSource.guard, Nat.add_mod, Nat.add_div]
      | less c d =>
          cases c <;> simp [Code.guard, SourceFormula.encode, BoundedSource.guard, BaseTerm.encode,
            Nat.add_mod, Nat.add_div, variables_calibration, eq_comm]

theorem literalSyntaxCode : BoundedSourceProgramsTargets.LiteralSyntaxCode := by
  intro p
  induction p with
  | equal a b => rw [Code.test]; simp [SourceFormula.encode, BoundedSource.test]
  | less a b => rw [Code.test]; simp [SourceFormula.encode, BoundedSource.test, Nat.add_mod]
  | negative p ih => rw [Code.test]; simp [SourceFormula.encode, BoundedSource.test, Nat.add_mod, Nat.add_div, ih]
  | conjunction p q ihp ihq => rw [Code.test]; simp [SourceFormula.encode, BoundedSource.test, Nat.add_mod, Nat.add_div, ihp, ihq]
  | existsNat i p ih => rw [Code.test]; simp [SourceFormula.encode, BoundedSource.test, Nat.add_mod, Nat.add_div, literalGuardCode i p, ih]

theorem literalAnswerCode : BoundedSourceProgramsTargets.LiteralAnswerCode := by
  intro values p
  induction p generalizing values with
  | equal a b =>
      rw [Code.answer]
      simp [SourceFormula.encode, BoundedSource.answer, ScopedPhiProgramsProof.actualZeroDefaultEvaluation values a,
        ScopedPhiProgramsProof.actualZeroDefaultEvaluation values b]
  | less a b =>
      rw [Code.answer]
      simp [SourceFormula.encode, BoundedSource.answer, Nat.add_mod, Nat.add_div,
        ScopedPhiProgramsProof.actualZeroDefaultEvaluation values a, ScopedPhiProgramsProof.actualZeroDefaultEvaluation values b]
  | negative p ih => rw [Code.answer]; simp [SourceFormula.encode, BoundedSource.answer, Nat.add_mod, Nat.add_div, ih]
  | conjunction p q ihp ihq => rw [Code.answer]; simp [SourceFormula.encode, BoundedSource.answer, Nat.add_mod, Nat.add_div, ihp, ihq]
  | existsNat i p ih =>
      have hu : ∀ n, PlainParameterDecision.valuation (Code.update values i n) =
          Function.update (PlainParameterDecision.valuation values) i n := by
        intro n; funext j; exact exactFiniteUpdate values i n j
      have hh : ∀ n, Code.answer (Code.update values i n) p.encode =
          BoundedSource.answer (Function.update (PlainParameterDecision.valuation values) i n) p := by
        intro n; rw [ih, hu]
      rw [Code.answer]
      cases hg : BoundedSource.guard i p with
      | none => simp [SourceFormula.encode, BoundedSource.answer, Nat.add_mod, Nat.add_div, literalGuardCode i p, hg]
      | some t => simp [SourceFormula.encode, BoundedSource.answer, Nat.add_mod, Nat.add_div,
          literalGuardCode i p, hg, ScopedPhiProgramsProof.actualZeroDefaultEvaluation values t, hh]

theorem decision_calibration (values : List Nat) (p : SourceFormula) :
    Code.decide values p.encode = BoundedSource.decide values p := by
  unfold Code.decide BoundedSource.decide
  rw [literalSyntaxCode p, literalAnswerCode values p]

theorem actualRawDecision : BoundedSourceProgramsTargets.ActualRawDecision := by
  intro values code
  have hc := decision_calibration values (SourceFormulaCodec.decode code)
  rw [SourceFormulaCodecProof.codeRoundtrip code] at hc
  rw [hc]
  exact BoundedSourceProof.actualDecision values (SourceFormulaCodec.decode code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsProof
