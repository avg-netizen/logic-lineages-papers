module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsFormulaProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsAnswerProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsProof
open FiniteSearchPrograms ScopedPhiProgramsGraph
attribute [local irreducible] Nat.sqrt Nat.unpair BoundedSourcePrograms.Code.guard

private def testAssemble (p : ScopedPhiProgramsGraph.Input) (results : List Bool) : Bool :=
  ScopedPhiPrograms.Code.test [] p.2 ||
    if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then false
    else if p.2 % 5 = 2 then results.getD 0 false
    else if p.2 % 5 = 3 then results.getD 0 false && results.getD 1 false
    else (BoundedSourcePrograms.Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2).isSome && results.getD 0 false

private theorem test_equation (p : ScopedPhiProgramsGraph.Input) :
    Code.test p.2 = testAssemble p ((formulaChildren false p).map (fun q => Code.test q.2)) := by
  rw [Code.test]
  split_ifs <;> simp_all [testAssemble, formulaChildren]

private theorem testAssemble_computable : Computable₂ testAssemble := by
  let A := ScopedPhiProgramsGraph.Input × List Bool
  have h0 : Computable (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 1)
  have hg : Computable (fun p : A => (BoundedSourcePrograms.Code.guard (p.1.2 / 5).unpair.1 (p.1.2 / 5).unpair.2).isSome) :=
    Primrec.option_isSome.to_comp.comp (BoundedSourceProgramsProof.guard_computable.comp
      ((left_primitive 5).to_comp.comp Computable.fst) ((right_primitive 5).to_comp.comp Computable.fst))
  have hs : Computable (fun p : A => ScopedPhiPrograms.Code.test [] p.1.2) :=
    ScopedPhiProgramsProof.test_computable.comp (Computable.const []) (Computable.snd.comp Computable.fst)
  have hf : Computable (fun p : A =>
      if p.1.2 % 5 = 0 ∨ p.1.2 % 5 = 1 then false
      else if p.1.2 % 5 = 2 then p.2.getD 0 false
      else if p.1.2 % 5 = 3 then p.2.getD 0 false && p.2.getD 1 false
      else (BoundedSourcePrograms.Code.guard (p.1.2 / 5).unpair.1 (p.1.2 / 5).unpair.2).isSome && p.2.getD 0 false) :=
    computable_ite (((tag_is 5 0).or (tag_is 5 1)).comp Primrec.fst).decide.to_comp (Computable.const false)
      (computable_ite ((tag_is 5 2).comp Primrec.fst).decide.to_comp h0
        (computable_ite ((tag_is 5 3).comp Primrec.fst).decide.to_comp (Primrec.and.to_comp.comp h0 h1)
          (Primrec.and.to_comp.comp hg h0)))
  exact Primrec.or.to_comp.comp hs hf

theorem test_computable : Computable Code.test := by
  have h := (BalancedBoxEvaluation.Graph.exactDecreasingGraph ScopedPhiProgramsGraph.Input Bool
    (formulaChildren false) testAssemble Prod.snd (formulaChildren_primitive false).to_comp
    testAssemble_computable Computable.snd (fun p => Code.test p.2)
    (formulaChildren_decreasing false) test_equation).2
  exact h.comp ((Computable.const []).pair Computable.id)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsProof
