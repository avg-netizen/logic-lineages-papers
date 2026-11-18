module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeCalibrationProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.CalibrationProof
open OrdinalComparison PolynomialGraphCompletion
open ExpressionCodeCalibrationProof

theorem test_code (r : Relation) (a b : Nat) :
    Code.test r.code a b = WordLinearDecisionCompletion.Formula.encode (outputTest r a b) := by
  cases r <;> rfl

theorem graph_code (rs : List Row) :
    Code.graph rs = WordLinearDecisionCompletion.Formula.encode (graphFormula rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [Code.graph,graphFormula,List.foldr_cons]
    change Code.conj (Code.equal r) (Code.graph rs) = _
    rw [ih]
    rfl

theorem positive_code (d : Nat) :
    Code.positive d = WordLinearDecisionCompletion.Formula.encode (positiveFormula d) := by
  have aux : ∀ is : List Nat,
      is.foldr (fun i q => Code.conj (Code.nonnegative (-1,[(1,i,[])])) q) 0 =
      WordLinearDecisionCompletion.Formula.encode
        (is.foldr (fun i q => .conj (.atom (.nonnegative (-1,[(1,i,[])]))) q) .top) := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih => simp only [List.foldr_cons,ih]; rfl
  exact aux (List.range d)

theorem program_heads (p : Source) : Code.heads (program p) = p.heads := by
  induction p with
  | truth b => cases b <;> simp [program,Code.heads,Source.heads]
  | atom r a b =>
    cases r <;> simp [program,Relation.code,Code.heads,Source.heads,
      instructions_calibration,instructions_headNames]
  | neg p ih =>
    simp only [Code.heads] at ih
    simpa [program,Code.heads,List.flatMap_append,Source.heads] using ih
  | conj p q ihp ihq | disj p q ihp ihq =>
    simp only [Code.heads] at ihp ihq
    simp [program,Code.heads,List.flatMap_append,ihp,ihq,Source.heads]

theorem program_run (p : Source) (start : Nat) (prior : List Row) (stack : List Nat) :
    (program p).foldl Code.step (start,prior,stack) =
      ((compile start p).1,prior++(compile start p).2.1,
       WordLinearDecisionCompletion.Formula.encode (compile start p).2.2::stack) := by
  induction p generalizing start prior stack with
  | truth b => cases b <;> simp [program,compile,Code.step,WordLinearDecisionCompletion.Formula.encode]
  | atom r a b =>
    have ha := rowMachineCalibration a start [] []
    have hb := rowMachineCalibration b (start+nodeCount a) [] []
    cases r <;> simp [program,compile,Code.step,Relation.code,instructions_calibration,
      ha,hb,List.append_assoc,Code.test,Code.equal,Code.nonnegative,Code.conj,
      outputTest,equality,WordLinearDecisionCompletion.Formula.encode,
      WordLinearDecisionCompletion.Atom.data]
  | neg p ih =>
    simp only [program,List.foldl_append,ih,List.foldl_cons,List.foldl_nil]
    simp [Code.step,compile,Code.neg,WordLinearDecisionCompletion.Formula.encode]
  | conj p q ihp ihq =>
    simp only [program,List.foldl_append,ihp,ihq,List.foldl_cons,List.foldl_nil]
    simp [Code.step,compile,Code.conj,WordLinearDecisionCompletion.Formula.encode,List.append_assoc]
  | disj p q ihp ihq =>
    simp only [program,List.foldl_append,ihp,ihq,List.foldl_cons,List.foldl_nil]
    simp [Code.step,compile,Code.disj,WordLinearDecisionCompletion.Formula.encode,List.append_assoc]

theorem full : Targets.LiteralCompiler := by
  intro d p
  simp only [Code.package,Code.decode,sourceCode,Encodable.encodek,Option.getD_some,
    program_run,List.nil_append,List.headD_cons,program_heads,positive_code,graph_code]
  rfl

end LogicLineages.StandardControlCurrent.PolynomialBoolean.CalibrationProof
