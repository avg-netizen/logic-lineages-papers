module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerTargets
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmGuardProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm Runner

abbrev WorkData := Row × Nat
abbrev CaseData := Nat × List (Nat × Row)

def encodeWork (w : Work) : WorkData := (w.row,Formula.encode w.guard)
def encodeCase (c : RowCase) : CaseData :=
  (Formula.encode c.guard,c.outcomes.map (fun o => (o.tag,o.row)))

def branchWork (parent : WorkData) (b : EncodedBranch) : Option WorkData :=
  if b.2.2.1 = 1 then some (b.2.2.2.2,6*Nat.pair parent.2 b.2.1+4) else none

def branchFinished (parent : WorkData) (b : EncodedBranch) : Option CaseData :=
  if b.2.2.1 = 0 then
    some (6*Nat.pair parent.2 b.2.1+4,[(b.2.2.2.1,b.2.2.2.2)]) else none

def initial (r : Row) : EncodedState := (rowTail r,[(r,0)],[])

/-- Numeric execution on actual encoded guards. It composes conjunction
codes and branches on action tags; it never decodes or tests a guard. -/
noncomputable def step (D maximum : Nat) (s : EncodedState) : EncodedState :=
  match s.2.1 with
  | [] => s
  | parent :: rest =>
      let bs := (stage D maximum parent.1).map encodeBranch
      (max s.1 (foldMax (bs.map Prod.fst)),bs.filterMap (branchWork parent)++rest,
        bs.filterMap (branchFinished parent)++s.2.2)

noncomputable def run (D maximum : Nat) (r : Row) (fuel : Nat) : EncodedState :=
  (step D maximum)^[fuel] (initial r)

theorem encoded_work_children (parent : Work) (bs : List Branch) :
    ((bs.map encodeBranch).filterMap (branchWork (encodeWork parent))) =
      (bs.filterMap (Runner.branchWork parent)).map encodeWork := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons,List.filterMap_cons]
      rw [ih]
      cases ha : b.action <;>
        simp [branchWork,Runner.branchWork,encodeBranch,encodeWork,ha,Formula.encode]

theorem encoded_finished_children (parent : Work) (bs : List Branch) :
    ((bs.map encodeBranch).filterMap (branchFinished (encodeWork parent))) =
      (bs.filterMap (Runner.branchFinished parent)).map encodeCase := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons,List.filterMap_cons]
      rw [ih]
      cases ha : b.action <;>
        simp [branchFinished,Runner.branchFinished,encodeBranch,encodeWork,encodeCase,ha,
          Formula.encode]

theorem initial_calibration (r : Row) : initial r = encodeState (Runner.initial r) := rfl

theorem step_calibration (D maximum : Nat) (s : State) :
    step D maximum (encodeState s) = encodeState (Runner.step D maximum s) := by
  cases s with
  | mk paid work finished =>
      cases work with
      | nil => rfl
      | cons parent rest =>
          let bs := stage D maximum parent.row
          change (max paid (foldMax ((bs.map encodeBranch).map Prod.fst)),
            (bs.map encodeBranch).filterMap (branchWork (encodeWork parent))++rest.map encodeWork,
            (bs.map encodeBranch).filterMap (branchFinished (encodeWork parent))++finished.map encodeCase) =
            (max paid (foldMax (bs.map Branch.tail)),
              ((bs.filterMap (Runner.branchWork parent))++rest).map encodeWork,
              ((bs.filterMap (Runner.branchFinished parent))++finished).map encodeCase)
          rw [encoded_work_children,encoded_finished_children]
          simp only [List.map_append,List.map_map,Function.comp_def,encodeBranch]

theorem run_calibration (D maximum : Nat) (r : Row) (fuel : Nat) :
    run D maximum r fuel = encodeState (Runner.run D maximum r fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [run,Runner.run,Function.iterate_succ_apply']
      change step D maximum (run D maximum r fuel) =
        encodeState (Runner.step D maximum (Runner.run D maximum r fuel))
      rw [ih,step_calibration]

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
