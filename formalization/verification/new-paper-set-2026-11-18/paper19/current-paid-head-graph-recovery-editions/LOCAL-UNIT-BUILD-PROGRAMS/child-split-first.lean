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

private theorem tasksProgram : Primrec tasks := by
  let F := ChildTask×Nat
  have n : Primrec (fun q : ChildTask => q.1.1.1-1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)
  have r : Primrec (fun q : ChildTask => q.1.2) := Primrec.snd.comp Primrec.fst
  have Γ := Primrec.list_append.comp (Primrec.fst.comp r) (Primrec.snd.comp (Primrec.snd.comp r))
  have a : Primrec (fun q : ChildTask => (q.1.1.1-1,q.1.2.1++q.1.2.2.2,q.2.1)) :=
    n.pair (Γ.pair (Primrec.fst.comp Primrec.snd))
  have b : Primrec (fun q : F => (q.1.1.1.1-1,q.1.1.2.1++q.1.1.2.2.2,q.2)) :=
    (n.comp Primrec.fst).pair ((Γ.comp Primrec.fst).pair Primrec.snd)
  have z : Primrec (fun q : ChildTask => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_casesOn z (singleProgram a) (pairListProgram (a.comp Primrec.fst) b).to₂

noncomputable def children (p : Policy) (q : FuelState) : List FuelState :=
  if q.1=0 then [] else
    match UnitContextSelectionCode.selectCode q.2.1 with
    | none => []
    | some r => ((selectedChild p (q,r)).map (fun k => tasks ((q,r),k))).getD []

theorem childrenProgram (p : Policy) (hp : PolicyShape.Effective p) : Computable (children p) := by
  have h : Primrec (fun q : FuelState => UnitContextSelectionCode.selectCode q.2.1) :=
    UnitContextSelectionCode.StatementChecks.primitive_recursive_selection.comp (Primrec.fst.comp Primrec.snd)
  let D := FuelState×SelectedSplit
  have tail : Computable (fun q : D => ((selectedChild p q).map (fun k => tasks (q,k))).getD []) :=
    Computable.option_getD (Computable.option_map (selectedProgram p hp) tasksProgram.to_comp.to₂) (Computable.const [])
  exact chooseProgram (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Computable.const [])
    (Computable.option_casesOn h.to_comp (Computable.const []) tail.to₂)

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
        cases hk : k.2.2.1 <;> simp [hq,tasks,hk] at h
        · subst r; omega
        · rcases h with rfl|rfl <;> omega

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode.BuildPrograms
