module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairTargets
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionProgramStatementChecks
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeProgramsProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairCodeProof
open PolynomialGraphCompletion Pair
open ExpressionCodeProgramsProof

theorem literalNumericPackage : PairTargets.LiteralNumericPackage := by
  intro n mode flag a b
  have ha := ExpressionProgramStatementChecks.instruction_code_calibration a
  have hb := ExpressionProgramStatementChecks.instruction_code_calibration b
  have ht := ExpressionProgramStatementChecks.instruction_code_calibration (.add a b)
  have hr := ExpressionProgramStatementChecks.row_machine_calibration (.add a b) n [] []
  unfold Code.package
  rw [ha.1,hb.1]
  change ((familyDegree (ExpressionCode.headNames (instructions (.add a b))),n),
      List.range (n+(instructions (.add a b)).length),
      (ExpressionCode.run (instructions (.add a b)) (n,[],[])).2.2,
      differenceRow (n+(instructions a).length-1)
        (n+(instructions a).length+(instructions b).length-1),(mode,flag)) = _
  rw [ht.2.2.2,ht.2.1,hr,ha.2.1,hb.2.1]
  rfl

private theorem difference_primitive : Primrec₂ differenceRow := by
  have hleft : Primrec (fun p : Nat × Nat => ((1 : Int),p.1,([] : Word))) :=
    (Primrec.const (1 : Int)).pair (Primrec.fst.pair (Primrec.const []))
  have hright : Primrec (fun p : Nat × Nat => ((-1 : Int),p.2,([] : Word))) :=
    (Primrec.const (-1 : Int)).pair (Primrec.snd.pair (Primrec.const []))
  exact (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp hleft (Primrec.list_cons.comp hright (Primrec.const [])))

theorem actualNumericProgram : PairTargets.ActualNumericProgram := by
  let A := Code.Input
  have hn : Primrec (fun p : A => p.1) := Primrec.fst
  have hm : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hl := instructions_primitive.comp (Primrec.fst.comp hc)
  have hr := instructions_primitive.comp (Primrec.snd.comp hc)
  have ho := Primrec.list_append.comp (Primrec.list_append.comp hl hr) (Primrec.const [(2,0)])
  have hll := Primrec.list_length.comp hl
  have hrl := Primrec.list_length.comp hr
  have hol := Primrec.list_length.comp ho
  have hstate := run_primitive.comp ho (hn.pair ((Primrec.const []).pair (Primrec.const [])))
  have hrows := Primrec.snd.comp (Primrec.snd.comp hstate)
  have hx := Primrec.nat_sub.comp (Primrec.nat_add.comp hn hll) (Primrec.const 1)
  have hy := Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hn hll) hrl) (Primrec.const 1)
  have hd := HeadProgramsProof.familyDegree_primitive.comp (headNames_primitive.comp ho)
  have hp := Primrec.list_range.comp (Primrec.nat_add.comp hn hol)
  exact (hd.pair hn).pair (hp.pair (hrows.pair ((difference_primitive.comp hx hy).pair (hm.pair hf))))
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairCodeProof
