module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminalTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsGraphProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminal
open OrdinalComparison.LayeredComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ScopedPhiProgramsGraph
open OriginalMixedTerminalTest (boundedNames)
attribute [local irreducible] Nat.sqrt Nat.unpair BaseTermPrograms.variablesCode

private def assembleNames (p : Input) (results : List (List Nat)) : List Nat :=
  if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then
    BaseTermPrograms.variablesCode (p.2 / 5).unpair.1 ++ BaseTermPrograms.variablesCode (p.2 / 5).unpair.2
  else if p.2 % 5 = 2 then results.getD 0 []
  else if p.2 % 5 = 3 then results.getD 0 [] ++ results.getD 1 []
  else (p.2 / 5).unpair.1 :: results.getD 0 []

private theorem equation (p : Input) :
    namesCode p.2 = assembleNames p ((formulaChildren false p).map (fun q => namesCode q.2)) := by
  rw [namesCode]
  split_ifs <;> simp_all [assembleNames,formulaChildren]

private theorem assembleComputable : Computable₂ assembleNames := by
  let A := Input × List (List Nat)
  have h0 : Computable (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Nat)).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Nat)).to_comp.comp Computable.snd (Computable.const 1)
  have l : Computable (fun p : A => (p.1.2/5).unpair.1) := ((left_primitive 5).comp Primrec.fst).to_comp
  have r : Computable (fun p : A => (p.1.2/5).unpair.2) := ((right_primitive 5).comp Primrec.fst).to_comp
  have leaves := Primrec.list_append.to_comp.comp (BalancedBoxEvaluation.Base.actualComputation.2.comp l)
    (BalancedBoxEvaluation.Base.actualComputation.2.comp r)
  have pair := Primrec.list_append.to_comp.comp h0 h1
  have binder := Primrec.list_cons.to_comp.comp l h0
  exact computable_ite (((tag_is 5 0).or (tag_is 5 1)).comp Primrec.fst).decide.to_comp leaves
    (computable_ite ((tag_is 5 2).comp Primrec.fst).decide.to_comp h0
      (computable_ite ((tag_is 5 3).comp Primrec.fst).decide.to_comp pair binder))

theorem namesComputable : Computable namesCode := by
  have h := (BalancedBoxEvaluation.Graph.exactDecreasingGraph Input (List Nat)
    (formulaChildren false) assembleNames Prod.snd (formulaChildren_primitive false).to_comp
    assembleComputable Computable.snd (fun p => namesCode p.2)
    (formulaChildren_decreasing false) equation).2
  exact h.comp ((Computable.const ([] : List Nat)).pair Computable.id)

theorem namesCalibrate (p : SourceFormula) : namesCode p.encode = boundedNames p := by
  induction p with
  | equal a b =>
      rw [namesCode]
      simp [SourceFormula.encode,boundedNames,BoundedSourceProgramsProof.variables_calibration]
  | less a b =>
      rw [namesCode]
      simp [SourceFormula.encode,boundedNames,Nat.add_mod,Nat.add_div,
        BoundedSourceProgramsProof.variables_calibration]
  | negative p ih =>
      rw [namesCode]
      simp [SourceFormula.encode,boundedNames,Nat.add_mod,Nat.add_div,ih]
  | conjunction p q ihp ihq =>
      rw [namesCode]
      simp [SourceFormula.encode,boundedNames,Nat.add_mod,Nat.add_div,ihp,ihq]
  | existsNat i p ih =>
      rw [namesCode]
      simp [SourceFormula.encode,boundedNames,Nat.add_mod,Nat.add_div,ih]

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminal
