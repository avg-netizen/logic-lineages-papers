module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitLocalProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitEffectiveProof
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum CurrentOneUnit
open LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof (exactDecreasingGraph)
open CurrentGroundAnnotationPrograms (chooseProgram)
open MatrixCode (singleProgram pairListProgram)

private abbrev S := Nat×List Nat×Nat
private abbrev Split := UnitContextSelectionCode.Split
private abbrev C := S × Split
private abbrev Task := C × Packet
private abbrev Result := Option Block
private abbrev A := S × List Result

private def selectedChild (p : Policy) (q : C) : Option Packet :=
  compileSelected p (q.2.1.length,q.1.2.1,q.1.2.2)

private theorem selectedProgram (p : Policy) (hp : PolicyShape.Effective p) : Computable (selectedChild p) := by
  have l : Primrec (fun q : C => q.2.1.length) := Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  have s : Primrec (fun q : C => q.1.2) := Primrec.snd.comp Primrec.fst
  exact ((CurrentOneUnit.effective.2 p hp).2).comp (l.pair s).to_comp

private def tasks (q : Task) : List S :=
  let n := q.1.1.1-1
  let Γ := q.1.2.1++q.1.2.2.2
  let a : S := (n,Γ,q.2.1)
  match q.2.2.1 with
  | none => [a]
  | some b => [a,(n,Γ,b)]

private theorem tasksProgram : Primrec tasks := by
  let F := Task×Nat
  have n : Primrec (fun q : Task => q.1.1.1-1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)
  have r : Primrec (fun q : Task => q.1.2) := Primrec.snd.comp Primrec.fst
  have Γ := Primrec.list_append.comp (Primrec.fst.comp r) (Primrec.snd.comp (Primrec.snd.comp r))
  have a : Primrec (fun q : Task => (q.1.1.1-1,q.1.2.1++q.1.2.2.2,q.2.1)) :=
    n.pair (Γ.pair (Primrec.fst.comp Primrec.snd))
  have b : Primrec (fun q : F => (q.1.1.1.1-1,q.1.1.2.1++q.1.1.2.2.2,q.2)) :=
    (n.comp Primrec.fst).pair ((Γ.comp Primrec.fst).pair Primrec.snd)
  have z : Primrec (fun q : Task => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_casesOn z (singleProgram a) (pairListProgram (a.comp Primrec.fst) b).to₂

private noncomputable def children (p : Policy) (q : S) : List S :=
  if q.1=0 then [] else
    match UnitContextSelectionCode.selectCode q.2.1 with
    | none => []
    | some r => ((selectedChild p (q,r)).map (fun k => tasks ((q,r),k))).getD []

private theorem childrenProgram (p : Policy) (hp : PolicyShape.Effective p) : Computable (children p) := by
  have h : Primrec (fun q : S => UnitContextSelectionCode.selectCode q.2.1) :=
    UnitContextSelectionCode.StatementChecks.primitive_recursive_selection.comp (Primrec.fst.comp Primrec.snd)
  let D := S×Split
  have tail : Computable (fun q : D => ((selectedChild p q).map (fun k => tasks (q,k))).getD []) :=
    Computable.option_getD (Computable.option_map (selectedProgram p hp) tasksProgram.to_comp.to₂) (Computable.const [])
  exact chooseProgram (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Computable.const [])
    (Computable.option_casesOn h.to_comp (Computable.const []) tail.to₂)

private theorem childDecrease (p : Policy) (q r : S) (h : r∈children p q) : r.1<q.1 := by
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

private noncomputable def resultPart (q : A×Packet) : Result := do
  let l ← q.1.2.getD 0 none
  let g := groundCount q.1.1.2.1
  let row := q.2.2.2.2
  match q.2.2.1 with
  | none => pure (freeBlock g row l)
  | some _ =>
    let r ← q.1.2.getD 1 none
    pure (activeBlock g row l r)

private theorem resultPartProgram : Computable resultPart := by
  let P := A×Packet
  let Z := P×Block
  have p : Primrec (fun q : Z => q.1.2) := Primrec.snd.comp Primrec.fst
  have g : Primrec (fun q : Z => groundCount q.1.1.1.2.1) := countProgram.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have row : Primrec (fun q : Z => q.1.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp p))
  have rs : Primrec (fun q : Z => q.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have t : Primrec (fun q : Z => q.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp p)
  have hfree : Computable (fun q : Z => some (freeBlock (groundCount q.1.1.1.2.1) q.1.2.2.2.2 q.2)) :=
    Computable.option_some_iff.mpr (freeBlockProgram.comp (g.pair (row.pair Primrec.snd)).to_comp)
  have R : Primrec (fun q : Z => q.1.1.2.getD 1 none) := (Primrec.list_getD none).comp rs (Primrec.const 1)
  have hact := Computable.option_map R.to_comp (activeBlockProgram.comp
    ((g.comp Primrec.fst).pair ((row.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to_comp.to₂
  have L : Primrec (fun q : P => q.1.2.getD 0 none) := (Primrec.list_getD none).comp
    (Primrec.snd.comp Primrec.fst) (Primrec.const 0)
  have h := Computable.option_bind L.to_comp
    (chooseProgram (Primrec.eq.comp t (Primrec.const none)) hfree hact).to₂
  apply h.of_eq
  intro q
  cases ht : q.2.2.1 <;> cases hl : q.1.2.getD 0 none <;> simp [resultPart,ht,hl,Option.map_eq_bind]

private noncomputable def assemble (p : Policy) (f : Nat→Nat) (q : S) (rs : List Result) : Result :=
  if q.1=0 then none else
    match UnitContextSelectionCode.selectCode q.2.1 with
    | none => (CurrentTreeInputCoverage.compile q.2.1 q.2.2).map (groundBlock p f)
    | some r => (selectedChild p (q,r)).bind fun k => resultPart ((q,rs),k)

private theorem assembleProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable₂ (assemble p f) := by
  have ctx : Primrec (fun q : A => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have a : Primrec (fun q : A => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hselect := UnitContextSelectionCode.StatementChecks.primitive_recursive_selection.comp ctx
  have hinput := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.2.comp ctx.to_comp a.to_comp
  have hbase : Computable (fun q : A => (CurrentTreeInputCoverage.compile q.1.2.1 q.1.2.2).map (groundBlock p f)) :=
    Computable.option_map hinput ((groundBlockProgram p hp f hc hf).comp Computable.snd).to₂
  let V := A×Split
  have hstep := (selectedProgram p hp).comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd : Primrec fun q : V => q.2)).to_comp
  have ht : Computable (fun q : V => (selectedChild p (q.1.1,q.2)).bind fun k => resultPart (q.1,k)) :=
    Computable.option_bind hstep (resultPartProgram.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  exact chooseProgram (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)) (Computable.const none)
    (Computable.option_casesOn hselect.to_comp hbase ht.to₂)

private theorem calibration (p : Policy) (f : Nat→Nat) (q : S) : blockFuel p f q.1 q.2.1 q.2.2 =
    assemble p f q ((children p q).map (fun q => blockFuel p f q.1 q.2.1 q.2.2)) := by
  rcases q with ⟨n,Γ,t⟩
  cases n with
  | zero => rfl
  | succ n =>
    cases h : UnitContextSelectionCode.selectCode Γ with
    | none => simp [children,assemble,blockFuel,h,Option.map_eq_bind]
    | some r =>
      rcases r with ⟨left,σ,right⟩
      cases hp : compileSelected p (left.length,Γ,t) with
      | none => simp [children,assemble,blockFuel,h,selectedChild,hp]
      | some k =>
        cases hk : k.2.2.1 <;> simp [children,assemble,blockFuel,h,selectedChild,hp,tasks,hk,resultPart]

theorem blockFuelProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : Nat×List Nat×Nat => blockFuel p f q.1 q.2.1 q.2.2) :=
  (exactDecreasingGraph S Result (children p) (assemble p f) Prod.fst (childrenProgram p hp)
    (assembleProgram p hp f hc hf) Computable.fst _ (childDecrease p) (calibration p f)).2

theorem blockProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : List Nat×Nat => block p f q.1 q.2) :=
  (blockFuelProgram p hp f hc hf).comp ((Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)).pair Primrec.id).to_comp

theorem effectiveMatrixUnitCodes : Targets.EffectiveMatrixUnitCodes :=
  ⟨MatrixCode.renameTermProgram,MatrixCode.renameFormulaProgram,MatrixCode.inputCodeProgram,
    fun p hp f hc hf => ⟨blockFuelProgram p hp f hc hf,blockProgram p hp f hc hf⟩⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
