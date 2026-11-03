module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecProof
open NumberedTypedRequests NumberedTypedEvaluation NumberedTypedEvaluationPrimrec

private theorem failureFixed {n : Nat} (arity : Fin n → Nat) (fuel : Nat) :
    (step arity)^[fuel] (none : State n) = none :=
  Function.iterate_fixed (by rfl) fuel

private theorem completionFixed {n : Nat} (arity : Fin n → Nat) (fuel : Nat) :
    (step arity)^[fuel] (some [] : State n) = some [] :=
  Function.iterate_fixed (by rfl) fuel

theorem iterationCalibration : NumberedTypedEvaluationPrimrecTargets.ActualIterationCalibration := by
  intro n arity fuel
  induction fuel with
  | zero =>
    intro requests
    cases requests <;> rfl
  | succ fuel ih =>
    intro requests
    cases requests with
    | nil =>
      simp only [run, completionFixed, done, evaluate]
    | cons request rest =>
      cases hexpand : expand arity request with
      | none =>
        simp only [run, Function.iterate_succ_apply, step, hexpand,
          Option.map_none, failureFixed, done, evaluate]
      | some children =>
        simpa only [run, Function.iterate_succ_apply, step, hexpand,
          Option.map_some, evaluate] using ih (children ++ rest)

theorem stepPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (step arity : State n → State n) := by
  have hnonempty : Primrec (fun p : Request n × List (Request n) =>
      (expand arity p.1).map (fun children => children ++ p.2)) :=
    Primrec.option_map
      ((NumberedRequestExpansionPrimrecProof.expansionPrimitive n arity).comp Primrec.fst)
      (Primrec.list_append.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have hwork : Primrec (fun requests : List (Request n) =>
      (List.casesOn requests (some []) (fun request rest =>
        (expand arity request).map (fun children => children ++ rest)) : State n)) :=
    Primrec.list_casesOn Primrec.id (Primrec.const (some []))
      (hnonempty.comp Primrec.snd).to₂
  refine (Primrec.option_bind₁ hwork).of_eq ?_
  intro state
  cases state with
  | none => rfl
  | some requests => cases requests <;> rfl

theorem donePrimitive (n : Nat) : Primrec (done : State n → Bool) := by
  have hwork : Primrec (fun requests : List (Request n) =>
      (List.casesOn requests true (fun _ _ => false) : Bool)) :=
    Primrec.list_casesOn Primrec.id (Primrec.const true) (Primrec.const false).to₂
  refine (Primrec.option_casesOn Primrec.id (Primrec.const false)
    (hwork.comp Primrec.snd).to₂).of_eq ?_
  intro state
  cases state with
  | none => rfl
  | some requests => cases requests <;> rfl

theorem runPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun input : Nat × List (Request n) => run arity input.1 input.2) := by
  unfold run
  exact Primrec.nat_iterate Primrec.fst (Primrec.option_some.comp Primrec.snd)
    ((stepPrimitive n arity).comp Primrec.snd).to₂

theorem evaluatorPrimitive : NumberedTypedEvaluationPrimrecTargets.ActualEvaluatorPrimitive := by
  intro n arity
  exact ((donePrimitive n).comp (runPrimitive n arity)).of_eq
    (fun input => iterationCalibration n arity input.1 input.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecProof
