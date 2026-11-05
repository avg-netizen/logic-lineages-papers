module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsTermProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionCodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
open ScopedPhiPrograms ScopedPhiProgramsGraph
attribute [local irreducible] Nat.sqrt Nat.unpair Code.value

private def testAssemble (p : ScopedPhiProgramsGraph.Input) (results : List Bool) : Bool :=
  if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then Code.termTest p.1 (p.2 / 5).unpair.1 && Code.termTest p.1 (p.2 / 5).unpair.2
  else if p.2 % 5 = 2 then results.getD 0 false
  else if p.2 % 5 = 3 then results.getD 0 false && results.getD 1 false
  else results.getD 0 false

private theorem test_equation (p : ScopedPhiProgramsGraph.Input) :
    Code.test p.1 p.2 = testAssemble p ((formulaChildren true p).map (fun q => Code.test q.1 q.2)) := by
  rw [Code.test]
  split_ifs <;> simp_all [testAssemble, formulaChildren]

private theorem testAssemble_computable : Computable₂ testAssemble := by
  let A := ScopedPhiProgramsGraph.Input × List Bool
  have h0 : Computable (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 1)
  have hl : Computable (fun p : A => Code.termTest p.1.1 (p.1.2 / 5).unpair.1) :=
    termTest_computable.comp (Computable.fst.comp Computable.fst) ((left_primitive 5).to_comp.comp Computable.fst)
  have hr : Computable (fun p : A => Code.termTest p.1.1 (p.1.2 / 5).unpair.2) :=
    termTest_computable.comp (Computable.fst.comp Computable.fst) ((right_primitive 5).to_comp.comp Computable.fst)
  exact computable_ite (((tag_is 5 0).or (tag_is 5 1)).comp Primrec.fst).decide.to_comp
    (Primrec.and.to_comp.comp hl hr)
    (computable_ite ((tag_is 5 2).comp Primrec.fst).decide.to_comp h0
      (computable_ite ((tag_is 5 3).comp Primrec.fst).decide.to_comp (Primrec.and.to_comp.comp h0 h1) h0))

theorem test_computable : Computable₂ Code.test :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph ScopedPhiProgramsGraph.Input Bool (formulaChildren true) testAssemble
    Prod.snd (formulaChildren_primitive true).to_comp testAssemble_computable Computable.snd
    (fun p => Code.test p.1 p.2) (formulaChildren_decreasing true) test_equation).2

private def freezeAssemble (p : ScopedPhiProgramsGraph.Input) (results : List Nat) : Nat :=
  if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then
    5 * Nat.pair (Code.freezeTerm p.1 (p.2 / 5).unpair.1) (Code.freezeTerm p.1 (p.2 / 5).unpair.2) + p.2 % 5
  else if p.2 % 5 = 2 then 5 * results.getD 0 0 + 2
  else if p.2 % 5 = 3 then 5 * Nat.pair (results.getD 0 0) (results.getD 1 0) + 3
  else 5 * Nat.pair (p.2 / 5).unpair.1 (results.getD 0 0) + 4

private theorem freezeFormula_equation (p : ScopedPhiProgramsGraph.Input) :
    Code.freezeFormula p.1 p.2 = freezeAssemble p ((formulaChildren false p).map (fun q => Code.freezeFormula q.1 q.2)) := by
  rw [Code.freezeFormula]
  split_ifs <;> simp_all [freezeAssemble, formulaChildren]

private theorem freezeAssemble_computable : Computable₂ freezeAssemble := by
  let A := ScopedPhiProgramsGraph.Input × List Nat
  have h0 : Computable (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD 0).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD 0).to_comp.comp Computable.snd (Computable.const 1)
  have hl : Computable (fun p : A => Code.freezeTerm p.1.1 (p.1.2 / 5).unpair.1) :=
    freezeTerm_computable.comp (Computable.fst.comp Computable.fst) ((left_primitive 5).to_comp.comp Computable.fst)
  have hr : Computable (fun p : A => Code.freezeTerm p.1.1 (p.1.2 / 5).unpair.2) :=
    freezeTerm_computable.comp (Computable.fst.comp Computable.fst) ((right_primitive 5).to_comp.comp Computable.fst)
  have ha : Computable (fun p : A => 5 * Nat.pair (Code.freezeTerm p.1.1 (p.1.2 / 5).unpair.1)
      (Code.freezeTerm p.1.1 (p.1.2 / 5).unpair.2) + p.1.2 % 5) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 5)
      (Primrec₂.natPair.to_comp.comp hl hr)) ((tag_primitive 5).to_comp.comp Computable.fst)
  have hn : Computable (fun p : A => 5 * p.2.getD 0 0 + 2) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 5) h0) (Computable.const 2)
  have hc : Computable (fun p : A => 5 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + 3) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 5)
      (Primrec₂.natPair.to_comp.comp h0 h1)) (Computable.const 3)
  have he : Computable (fun p : A => 5 * Nat.pair (p.1.2 / 5).unpair.1 (p.2.getD 0 0) + 4) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 5)
      (Primrec₂.natPair.to_comp.comp ((left_primitive 5).to_comp.comp Computable.fst) h0)) (Computable.const 4)
  exact computable_ite (((tag_is 5 0).or (tag_is 5 1)).comp Primrec.fst).decide.to_comp ha
    (computable_ite ((tag_is 5 2).comp Primrec.fst).decide.to_comp hn
      (computable_ite ((tag_is 5 3).comp Primrec.fst).decide.to_comp hc he))

theorem freezeFormula_computable : Computable₂ Code.freezeFormula :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph ScopedPhiProgramsGraph.Input Nat (formulaChildren false) freezeAssemble
    Prod.snd (formulaChildren_primitive false).to_comp freezeAssemble_computable Computable.snd
    (fun p => Code.freezeFormula p.1 p.2) (formulaChildren_decreasing false) freezeFormula_equation).2

theorem decide_computable : Computable₂ Code.decide := by
  have ht : Computable (fun p : List Nat × Nat => Code.test [] p.2) :=
    test_computable.comp (Computable.const []) Computable.snd
  have hv : Computable (fun p : List Nat × Nat => AdditiveParameterDecision.Code.decide p.1 (Code.freezeFormula p.1 p.2)) :=
    AdditiveParameterDecisionProof.actualNumericProgram.to_comp.comp Computable.fst freezeFormula_computable
  apply (Computable.cond ht hv (Computable.const none)).of_eq
  intro p
  unfold Code.decide
  cases Code.test [] p.2 <;> rfl

theorem actualNumericPrograms : ScopedPhiProgramsTargets.ActualNumericPrograms :=
  ⟨bound_primitive, table_primitive, value_computable, termTest_computable, test_computable,
    freezeTerm_computable, freezeFormula_computable, decide_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
