module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseGuardPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestExpansionPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationProof
open Source NumberedAuxiliaryCoding NumberedRequestWeight NumberedUniverseEvaluation
open NumberedTypedRequests (Request expand)
open NumberedUniverseRequests

private theorem requestExpansion {n : Nat} (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (request : Request n) :
    valid arity symbols S request = expandedValid arity symbols S request := by
  cases request with
  | term Gamma tau code =>
    exact NumberedUniverseRequestsProof.termExpansion n arity symbols S Gamma tau code
  | arguments Gamma types code =>
    exact NumberedUniverseRequestsProof.argumentsExpansion n arity symbols S Gamma types code

private theorem expansionPreserves {n : Nat} (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (request : Request n)
    (children rest : List (Request n))
    (hguard : NumberedUniverseRequests.guard arity symbols S request = true)
    (hexpand : expand arity request = some children) :
    (children ++ rest).all (valid arity symbols S) =
      (request :: rest).all (valid arity symbols S) := by
  simp only [List.all_append, List.all_cons]
  rw [requestExpansion arity symbols S request]
  simp [expandedValid, hguard, hexpand]

private theorem failedGuard {n : Nat} (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (request : Request n)
    (rest : List (Request n)) (hguard : NumberedUniverseRequests.guard arity symbols S request = false) :
    (request :: rest).all (valid arity symbols S) = false := by
  rw [List.all_cons, requestExpansion arity symbols S request]
  simp [expandedValid, hguard]

private theorem failedExpansion {n : Nat} (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (request : Request n)
    (rest : List (Request n)) (hexpand : expand arity request = none) :
    (request :: rest).all (valid arity symbols S) = false := by
  rw [List.all_cons, requestExpansion arity symbols S request]
  simp [expandedValid, hexpand]

private theorem requestWeightPositive {n : Nat} (request : Request n) :
    0 < requestWeight request := by
  cases request with
  | term Gamma tau code =>
    cases code <;> simp [requestWeight, codeWeight]
  | arguments Gamma types code =>
    cases code <;> simp [requestWeight, codeWeight]

theorem anyFuelSound : NumberedUniverseEvaluationTargets.AnyFuelSound := by
  intro n arity symbols S fuel
  induction fuel with
  | zero =>
    intro requests h
    cases requests with
    | nil => rfl
    | cons request rest => simp [evaluate] at h
  | succ fuel ih =>
    intro requests h
    cases requests with
    | nil => rfl
    | cons request rest =>
      cases hguard : NumberedUniverseRequests.guard arity symbols S request with
      | false => simp [evaluate, hguard] at h
      | true =>
        cases hexpand : expand arity request with
        | none => simp [evaluate, hguard, hexpand] at h
        | some children =>
          have hnext : evaluate arity symbols S fuel (children ++ rest) = true := by
            simpa [evaluate, hguard, hexpand] using h
          exact (expansionPreserves arity symbols S request children rest hguard hexpand).symm.trans
            (ih (children ++ rest) hnext)

theorem sufficientFuelExact : NumberedUniverseEvaluationTargets.SufficientFuelExact := by
  intro n arity symbols S fuel
  induction fuel with
  | zero =>
    intro requests hbound
    cases requests with
    | nil => rfl
    | cons request rest =>
      have hpositive := requestWeightPositive request
      have hzero : requestWeight request + workWeight rest ≤ 0 := by
        simpa [workWeight] using hbound
      omega
  | succ fuel ih =>
    intro requests hbound
    cases requests with
    | nil => rfl
    | cons request rest =>
      cases hguard : NumberedUniverseRequests.guard arity symbols S request with
      | false =>
        rw [evaluate, hguard]
        exact (failedGuard arity symbols S request rest hguard).symm
      | true =>
        cases hexpand : expand arity request with
        | none =>
          rw [evaluate, hguard, hexpand]
          exact (failedExpansion arity symbols S request rest hexpand).symm
        | some children =>
          have hdecrease := NumberedRequestWeightProof.replacementDecrease
            n arity request children rest hexpand
          have hnext : workWeight (children ++ rest) ≤ fuel := by omega
          calc
            evaluate arity symbols S (fuel + 1) (request :: rest) =
                evaluate arity symbols S fuel (children ++ rest) := by
              simp [evaluate, hguard, hexpand]
            _ = (children ++ rest).all (valid arity symbols S) := ih (children ++ rest) hnext
            _ = (request :: rest).all (valid arity symbols S) :=
              expansionPreserves arity symbols S request children rest hguard hexpand

private theorem failureFixed {n : Nat} (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (fuel : Nat) :
    (step arity symbols S)^[fuel] (none : State n) = none :=
  Function.iterate_fixed (by rfl) fuel

private theorem completionFixed {n : Nat} (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (fuel : Nat) :
    (step arity symbols S)^[fuel] (some [] : State n) = some [] :=
  Function.iterate_fixed (by rfl) fuel

theorem iterationCalibration : NumberedUniverseEvaluationTargets.ActualIterationCalibration := by
  intro n arity symbols S fuel
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
      cases hguard : NumberedUniverseRequests.guard arity symbols S request with
      | false =>
        simp [run, Function.iterate_succ_apply, step, hguard, failureFixed, done, evaluate]
      | true =>
        cases hexpand : expand arity request with
        | none =>
          simp [run, Function.iterate_succ_apply, step, hguard, hexpand,
            failureFixed, done, evaluate]
        | some children =>
          simpa [run, Function.iterate_succ_apply, step, hguard, hexpand, evaluate]
            using ih (children ++ rest)

theorem stepPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : (List (Fin n) × List Ty) × State n =>
      step arity p.1.1 p.1.2 p.2) := by
  have hexpansion : Primrec (fun p : (List (Fin n) × List Ty) ×
      (Request n × List (Request n)) =>
      (expand arity p.2.1).map (fun children => children ++ p.2.2)) :=
    Primrec.option_map
      (f := fun p : (List (Fin n) × List Ty) × (Request n × List (Request n)) =>
        expand arity p.2.1)
      (g := fun (p : (List (Fin n) × List Ty) × (Request n × List (Request n)))
        (children : List (Request n)) => children ++ p.2.2)
      ((NumberedRequestExpansionPrimrecProof.expansionPrimitive n arity).comp
        (g := fun p : (List (Fin n) × List Ty) × (Request n × List (Request n)) => p.2.1)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.list_append.comp Primrec.snd
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  have hguard : Primrec (fun p : (List (Fin n) × List Ty) ×
      (Request n × List (Request n)) => NumberedUniverseRequests.guard arity p.1.1 p.1.2 p.2.1) :=
    (NumberedUniverseGuardPrimrecProof.guardPrimitive n arity).comp
      (g := fun p : (List (Fin n) × List Ty) × (Request n × List (Request n)) =>
        (p.1, p.2.1))
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hnonempty : Primrec (fun p : (List (Fin n) × List Ty) ×
      (Request n × List (Request n)) =>
      bif NumberedUniverseRequests.guard arity p.1.1 p.1.2 p.2.1 then
        (expand arity p.2.1).map (fun children => children ++ p.2.2)
      else (none : State n)) :=
    Primrec.cond hguard hexpansion (Primrec.const none)
  have hwork : Primrec (fun p : (List (Fin n) × List Ty) × List (Request n) =>
      (List.casesOn p.2 (some []) (fun request rest =>
        bif NumberedUniverseRequests.guard arity p.1.1 p.1.2 request then
          (expand arity request).map (fun children => children ++ rest)
        else none) : State n)) :=
    Primrec.list_casesOn
      (f := fun p : (List (Fin n) × List Ty) × List (Request n) => p.2)
      (g := fun _ : (List (Fin n) × List Ty) × List (Request n) => (some [] : State n))
      (h := fun (p : (List (Fin n) × List Ty) × List (Request n))
        (payload : Request n × List (Request n)) =>
        bif NumberedUniverseRequests.guard arity p.1.1 p.1.2 payload.1 then
          (expand arity payload.1).map (fun children => children ++ payload.2)
        else none)
      Primrec.snd (Primrec.const (some []))
      ((hnonempty.comp
        (g := fun p : ((List (Fin n) × List Ty) × List (Request n)) ×
          (Request n × List (Request n)) => (p.1.1, p.2))
        ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)
  have hstate : Primrec (fun p : (List (Fin n) × List Ty) × State n =>
      p.2.bind (fun requests =>
        (List.casesOn requests (some []) (fun request rest =>
          bif NumberedUniverseRequests.guard arity p.1.1 p.1.2 request then
            (expand arity request).map (fun children => children ++ rest)
          else none) : State n))) :=
    Primrec.option_bind
      (f := fun p : (List (Fin n) × List Ty) × State n => p.2)
      (g := fun (p : (List (Fin n) × List Ty) × State n) (requests : List (Request n)) =>
        (List.casesOn requests (some []) (fun request rest =>
          bif NumberedUniverseRequests.guard arity p.1.1 p.1.2 request then
            (expand arity request).map (fun children => children ++ rest)
          else none) : State n))
      Primrec.snd
      ((hwork.comp
        (g := fun p : ((List (Fin n) × List Ty) × State n) × List (Request n) =>
          (p.1.1, p.2))
        ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)
  refine hstate.of_eq ?_
  intro p
  rcases p with ⟨window, state⟩
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
    Primrec (fun p : (List (Fin n) × List Ty) × Nat × List (Request n) =>
      run arity p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold run
  exact Primrec.nat_iterate
    (f := fun p : (List (Fin n) × List Ty) × Nat × List (Request n) => p.2.1)
    (g := fun p : (List (Fin n) × List Ty) × Nat × List (Request n) => some p.2.2)
    (h := fun (p : (List (Fin n) × List Ty) × Nat × List (Request n))
      (state : State n) => step arity p.1.1 p.1.2 state)
    (Primrec.fst.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
    ((stepPrimitive n arity).comp
      (g := fun p : ((List (Fin n) × List Ty) × Nat × List (Request n)) × State n =>
        (p.1.1, p.2))
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem evaluatorPrimitive : NumberedUniverseEvaluationTargets.ActualEvaluatorPrimitive := by
  intro n arity
  exact ((donePrimitive n).comp (runPrimitive n arity)).of_eq
    (fun p : (List (Fin n) × List Ty) × Nat × List (Request n) =>
      iterationCalibration n arity p.1.1 p.1.2 p.2.1 p.2.2)

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseEvaluationProof
