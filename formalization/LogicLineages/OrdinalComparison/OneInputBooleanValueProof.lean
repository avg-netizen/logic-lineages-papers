module
public import LogicLineages.OrdinalComparison.OneInputBooleanTargets
public import LogicLineages.OrdinalComparison.PositiveInputPlugProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneInputBoolean

theorem run_compile (formula : OneInputBooleanExpr) (x : Nat) (stack : List Bool) :
    encodedOneInputBooleanRun (oneInputBooleanCompile formula) x stack=
      actualOneInputBooleanValue formula x::stack := by
  induction formula generalizing stack with
  | truth value =>
    cases value <;> rfl
  | atom relation E F =>
    cases relation <;>
      simp [encodedOneInputBooleanRun,oneInputBooleanCompile,encodedOneInputBooleanStep,
        oneInputOrderRelationCode,encodedPositiveEvaluationCorrect E x,encodedPositiveEvaluationCorrect F x,actualOneInputBooleanValue]
  | neg formula ih =>
    change ((oneInputBooleanCompile formula)++[(5,0,0)]).foldl _ stack=_
    rw [List.foldl_append]
    change encodedOneInputBooleanStep x (5,0,0)
      (encodedOneInputBooleanRun (oneInputBooleanCompile formula) x stack)=_
    rw [ih]
    rfl
  | conj left right ihL ihR =>
    change ((oneInputBooleanCompile left)++(oneInputBooleanCompile right)++[(6,0,0)]).foldl _ stack=_
    rw [List.foldl_append,List.foldl_append]
    change encodedOneInputBooleanStep x (6,0,0)
      (encodedOneInputBooleanRun (oneInputBooleanCompile right) x
        (encodedOneInputBooleanRun (oneInputBooleanCompile left) x stack))=_
    rw [ihL,ihR]
    rfl
  | disj left right ihL ihR =>
    change ((oneInputBooleanCompile left)++(oneInputBooleanCompile right)++[(7,0,0)]).foldl _ stack=_
    rw [List.foldl_append,List.foldl_append]
    change encodedOneInputBooleanStep x (7,0,0)
      (encodedOneInputBooleanRun (oneInputBooleanCompile right) x
        (encodedOneInputBooleanRun (oneInputBooleanCompile left) x stack))=_
    rw [ihL,ihR]
    rfl

theorem source_value : Targets.ActualOneInputBooleanValue := by
  intro formula hv x
  unfold encodedOneInputBooleanValue
  rw [run_compile]
  rfl

end LogicLineages.OrdinalComparison.OneInputBoolean
