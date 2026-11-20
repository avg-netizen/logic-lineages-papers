module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitLocalProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitEffectiveProof
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode.BuildPrograms
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum CurrentOneUnit
open LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof (exactDecreasingGraph)
open CurrentGroundAnnotationPrograms (chooseProgram)
open MatrixCode (singleProgram pairListProgram)

abbrev FuelState := Nat×List Nat×Nat
abbrev SelectedSplit := UnitContextSelectionCode.Split
abbrev SelectionInput := FuelState × SelectedSplit
abbrev ChildTask := SelectionInput × Packet
abbrev BlockResult := Option Block
abbrev AssemblyInput := FuelState × List BlockResult

def selectedChild (p : Policy) (q : SelectionInput) : Option Packet :=
  compileSelected p (q.2.1.length,q.1.2.1,q.1.2.2)

theorem selectedProgram (p : Policy) (hp : PolicyShape.Effective p) : Computable (selectedChild p) := by
  have l : Primrec (fun q : SelectionInput => q.2.1.length) := Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  have s : Primrec (fun q : SelectionInput => q.1.2) := Primrec.snd.comp Primrec.fst
  exact ((CurrentOneUnit.effective.2 p hp).2).comp (l.pair s).to_comp

def tasks (q : ChildTask) : List FuelState :=
  let n := q.1.1.1-1
  let Γ := q.1.2.1++q.1.2.2.2
  let a : FuelState := (n,Γ,q.2.1)
  match q.2.2.1 with
  | none => [a]
  | some b => [a,(n,Γ,b)]

/-- Only the next fuel, context, and two child codes affect this list. -/
private abbrev TaskInputs := (Nat × List Nat) × Nat × Option Nat

private def taskInputs (q : ChildTask) : TaskInputs :=
  ((q.1.1.1-1,q.1.2.1++q.1.2.2.2),q.2.1,q.2.2.1)

private def taskList (x : TaskInputs) : List FuelState :=
  let a := (x.1.1,x.1.2,x.2.1)
  match x.2.2 with
  | none => [a]
  | some b => [a,(x.1.1,x.1.2,b)]

private theorem taskInputsProgram : Primrec taskInputs := by
  have n : Primrec (fun q : ChildTask => q.1.1.1-1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)
  have r : Primrec (fun q : ChildTask => q.1.2) := Primrec.snd.comp Primrec.fst
  have ctx := Primrec.list_append.comp (Primrec.fst.comp r) (Primrec.snd.comp (Primrec.snd.comp r))
  have first : Primrec (fun q : ChildTask => q.2.1) := Primrec.fst.comp Primrec.snd
  have second : Primrec (fun q : ChildTask => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact (n.pair ctx).pair (first.pair second)

private theorem taskListProgram : Primrec taskList := by
  have n : Primrec (fun x : TaskInputs => x.1.1) := Primrec.fst.comp Primrec.fst
  have ctx : Primrec (fun x : TaskInputs => x.1.2) := Primrec.snd.comp Primrec.fst
  have a : Primrec (fun x : TaskInputs => (x.1.1,x.1.2,x.2.1)) :=
    n.pair (ctx.pair (Primrec.fst.comp Primrec.snd))
  have b : Primrec (fun q : TaskInputs × Nat => (q.1.1.1,q.1.1.2,q.2)) :=
    (n.comp Primrec.fst).pair ((ctx.comp Primrec.fst).pair Primrec.snd)
  have z : Primrec (fun x : TaskInputs => x.2.2) := Primrec.snd.comp Primrec.snd
  have casesProgram := Primrec.option_casesOn z (singleProgram a)
    (pairListProgram (a.comp Primrec.fst) b).to₂
  exact casesProgram.of_eq (g := taskList) (fun x => by
    cases hz : x.2.2 <;> simp [taskList,hz])

section
attribute [local irreducible] taskInputs taskList tasks
private theorem tasksProgram : Primrec tasks :=
  (taskListProgram.comp taskInputsProgram).of_eq (fun q => by
    unfold taskList taskInputs tasks
    rfl)
end

noncomputable def children (p : Policy) (q : FuelState) : List FuelState :=
  if q.1=0 then [] else
    match UnitContextSelectionCode.selectCode q.2.1 with
    | none => []
    | some r => ((selectedChild p (q,r)).map (fun k => tasks ((q,r),k))).getD []

private noncomputable def selectedTasks (p : Policy) (q : SelectionInput) : List FuelState :=
  ((selectedChild p q).map (fun k => tasks (q,k))).getD []

section
attribute [local irreducible] selectedChild tasks
private theorem selectedTasksProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (selectedTasks p) := by
  unfold selectedTasks
  exact Computable.option_getD
    (Computable.option_map (selectedProgram p hp) tasksProgram.to_comp.to₂) (Computable.const [])
end

private noncomputable def nextTasks (p : Policy) (q : FuelState) : List FuelState :=
  match UnitContextSelectionCode.selectCode q.2.1 with
  | none => []
  | some r => selectedTasks p (q,r)

section
attribute [local irreducible] selectedTasks
private theorem nextTasksProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (nextTasks p) := by
  have h : Primrec (fun q : FuelState => UnitContextSelectionCode.selectCode q.2.1) :=
    UnitContextSelectionCode.StatementChecks.primitive_recursive_selection.comp (Primrec.fst.comp Primrec.snd)
  have casesProgram := Computable.option_casesOn h.to_comp
    (Computable.const ([] : List FuelState)) (selectedTasksProgram p hp).to₂
  exact casesProgram.of_eq (g := nextTasks p) (fun q => by
    cases hz : UnitContextSelectionCode.selectCode q.2.1 <;> simp [nextTasks,hz])
end

section
attribute [local irreducible] nextTasks
theorem childrenProgram (p : Policy) (hp : PolicyShape.Effective p) : Computable (children p) := by
  have h : Computable (fun q : FuelState => if q.1=0 then [] else nextTasks p q) :=
    chooseProgram (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Computable.const []) (nextTasksProgram p hp)
  exact h.of_eq (fun q => by unfold children nextTasks selectedTasks; rfl)
end

theorem childDecrease (p : Policy) (q r : FuelState) (h : r∈children p q) : r.1<q.1 := by
  unfold children at h
  split at h
  · simp at h
  · rename_i hp
    split at h
    · simp at h
    · rename_i s hs
      cases hq : selectedChild p (q,s) with
      | none => simp [hq] at h
      | some k =>
        cases hk : k.2.1 <;> simp [hq,tasks,hk] at h
        · subst r; omega
        · rcases h with rfl|rfl <;> omega

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode.BuildPrograms
