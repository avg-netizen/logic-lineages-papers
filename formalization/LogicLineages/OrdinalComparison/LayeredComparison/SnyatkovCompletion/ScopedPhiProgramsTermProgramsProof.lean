module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsGraphProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
open ScopedPhiPrograms ScopedPhiProgramsGraph
attribute [local irreducible] Nat.sqrt Nat.unpair BaseTermPrograms.variablesCode

private def termAssemble (p : ScopedPhiProgramsGraph.Input) (results : List Bool) : Bool :=
  if p.2 % 4 = 0 ∨ p.2 % 4 = 1 then true
  else if p.2 % 4 = 2 then results.getD 0 false && results.getD 1 false
  else (BaseTermPrograms.variablesCode (p.2 / 4)).all (fun i => !p.1.contains i)

private theorem term_equation (p : ScopedPhiProgramsGraph.Input) :
    Code.termTest p.1 p.2 = termAssemble p ((termChildren p).map (fun q => Code.termTest q.1 q.2)) := by
  rw [Code.termTest]
  by_cases h0 : p.2 % 4 = 0 ∨ p.2 % 4 = 1
  · have h2 : p.2 % 4 ≠ 2 := by omega
    simp [termAssemble, termChildren, h0, h2]
  · by_cases h2 : p.2 % 4 = 2 <;> simp [termAssemble, termChildren, h0, h2]

private theorem termAssemble_computable : Computable₂ termAssemble := by
  let A := ScopedPhiProgramsGraph.Input × List Bool
  have h0 : Computable (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 1)
  have hv : Computable (fun p : A => BaseTermPrograms.variablesCode (p.1.2 / 4)) :=
    BalancedBoxEvaluation.Base.actualComputation.2.comp ((quotient_primitive 4).to_comp.comp Computable.fst)
  have hp : Computable (fun p : A => (BaseTermPrograms.variablesCode (p.1.2 / 4)).all (fun i => !p.1.1.contains i)) :=
    avoids_primitive.to_comp.comp hv (Computable.fst.comp Computable.fst)
  exact computable_ite (((tag_is 4 0).or (tag_is 4 1)).comp Primrec.fst).decide.to_comp (Computable.const true)
    (computable_ite ((tag_is 4 2).comp Primrec.fst).decide.to_comp (Primrec.and.to_comp.comp h0 h1) hp)

theorem termTest_computable : Computable₂ Code.termTest :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph ScopedPhiProgramsGraph.Input Bool termChildren termAssemble
    Prod.snd termChildren_primitive.to_comp termAssemble_computable Computable.snd
    (fun p => Code.termTest p.1 p.2) termChildren_decreasing term_equation).2

private def freezeTermAssemble (p : ScopedPhiProgramsGraph.Input) (results : List Nat) : Nat :=
  if p.2 % 4 = 0 ∨ p.2 % 4 = 1 then p.2
  else if p.2 % 4 = 2 then 4 * Nat.pair (results.getD 0 0) (results.getD 1 0) + 2
  else 4 * Code.value p.1 p.2

private theorem freezeTerm_equation (p : ScopedPhiProgramsGraph.Input) :
    Code.freezeTerm p.1 p.2 = freezeTermAssemble p ((termChildren p).map (fun q => Code.freezeTerm q.1 q.2)) := by
  rw [Code.freezeTerm]
  by_cases h0 : p.2 % 4 = 0 ∨ p.2 % 4 = 1
  · have h2 : p.2 % 4 ≠ 2 := by omega
    simp [freezeTermAssemble, termChildren, h0, h2]
  · by_cases h2 : p.2 % 4 = 2 <;> simp [freezeTermAssemble, termChildren, h0, h2]

private theorem freezeTermAssemble_computable : Computable₂ freezeTermAssemble := by
  let A := ScopedPhiProgramsGraph.Input × List Nat
  have h0 : Computable (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD 0).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD 0).to_comp.comp Computable.snd (Computable.const 1)
  have ha : Computable (fun p : A => 4 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + 2) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 4)
      (Primrec₂.natPair.to_comp.comp h0 h1)) (Computable.const 2)
  have hp : Computable (fun p : A => 4 * Code.value p.1.1 p.1.2) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 4) (value_computable.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.fst))
  exact computable_ite (((tag_is 4 0).or (tag_is 4 1)).comp Primrec.fst).decide.to_comp (Computable.snd.comp Computable.fst)
    (computable_ite ((tag_is 4 2).comp Primrec.fst).decide.to_comp ha hp)

theorem freezeTerm_computable : Computable₂ Code.freezeTerm :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph ScopedPhiProgramsGraph.Input Nat termChildren freezeTermAssemble
    Prod.snd termChildren_primitive.to_comp freezeTermAssemble_computable Computable.snd
    (fun p => Code.freezeTerm p.1 p.2) termChildren_decreasing freezeTerm_equation).2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsProof
