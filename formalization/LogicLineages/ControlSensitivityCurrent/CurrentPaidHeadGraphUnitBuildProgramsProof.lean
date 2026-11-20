module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitChildProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum CurrentOneUnit
open LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof (exactDecreasingGraph)
open CurrentGroundAnnotationPrograms (chooseProgram)
open MatrixCode (singleProgram pairListProgram)

open BuildPrograms

private noncomputable def resultPart (q : AssemblyInput×Packet) : BlockResult := do
  let l ← q.1.2.getD 0 none
  let g := groundCount q.1.1.2.1
  let row := q.2.2.2.2
  match q.2.2.1 with
  | none => pure (freeBlock g row l)
  | some _ =>
    let r ← q.1.2.getD 1 none
    pure (activeBlock g row l r)

private def mapResult {I X Y} (f : I × X → Y) (q : I × Option X) : Option Y :=
  q.2.map (fun x => f (q.1,x))

private theorem mapResultProgram {I X Y} [Primcodable I] [Primcodable X] [Primcodable Y]
    {f : I × X → Y} (hf : Computable f) : Computable (mapResult f) := by
  unfold mapResult
  exact Computable.option_map Computable.snd
    (hf.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂

private def pairResults (q : BlockResult × BlockResult) : Option (Block × Block) :=
  q.1.bind (fun l => q.2.map (fun r => (l,r)))

private theorem pairResultsProgram : Computable pairResults := by
  have second : Computable (fun q : (BlockResult × BlockResult) × Block =>
      q.1.2.map (fun r => (q.2,r))) :=
    (mapResultProgram (Computable.id : Computable (fun x : Block × Block => x))).comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact Computable.option_bind Computable.fst second.to₂

private abbrev ResultInput := AssemblyInput × Packet
private abbrev RowInput := Nat × LinearCode
private def rowInput (q : ResultInput) : RowInput := (groundCount q.1.1.2.1,q.2.2.2.2)

private theorem rowInputProgram : Primrec rowInput := by
  have g : Primrec (fun q : ResultInput => groundCount q.1.1.2.1) :=
    countProgram.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have row : Primrec (fun q : ResultInput => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact g.pair row

private def withRow {X} (q : RowInput × X) : Nat × LinearCode × X :=
  (q.1.1,q.1.2,q.2)

private theorem withRowProgram {X} [Primcodable X] : Primrec (@withRow X) :=
  (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)

private def emitFree (q : RowInput × Block) : Block :=
  let a := withRow q
  freeBlock a.1 a.2.1 a.2.2

private def emitActive (q : RowInput × (Block × Block)) : Block :=
  let a := withRow q
  activeBlock a.1 a.2.1 a.2.2.1 a.2.2.2

section
attribute [local irreducible] withRow freeBlock activeBlock
private theorem emitFreeProgram : Computable emitFree := by
  unfold emitFree
  exact freeBlockProgram.comp withRowProgram.to_comp
private theorem emitActiveProgram : Computable emitActive := by
  unfold emitActive
  exact activeBlockProgram.comp withRowProgram.to_comp
end

private def resultAt (i : Nat) (q : ResultInput) : BlockResult := q.1.2.getD i none
private theorem resultAtProgram (i : Nat) : Primrec (resultAt i) :=
  (Primrec.list_getD none).comp (Primrec.snd.comp Primrec.fst) (Primrec.const i)

private def assembleResult (q : ResultInput) : BlockResult :=
  if q.2.2.1 = none then mapResult emitFree (rowInput q,resultAt 0 q)
  else mapResult emitActive (rowInput q,pairResults (resultAt 0 q,resultAt 1 q))

section
attribute [local irreducible] mapResult emitFree emitActive rowInput resultAt pairResults
private theorem assembleResultProgram : Computable assembleResult := by
  have tag : Primrec (fun q : ResultInput => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have blocks := pairResultsProgram.comp ((resultAtProgram 0).pair (resultAtProgram 1)).to_comp
  unfold assembleResult
  exact chooseProgram (Primrec.eq.comp tag (Primrec.const none))
    ((mapResultProgram emitFreeProgram).comp (rowInputProgram.pair (resultAtProgram 0)).to_comp)
    ((mapResultProgram emitActiveProgram).comp (rowInputProgram.to_comp.pair blocks))
end

private theorem resultPartProgram : Computable resultPart := by
  apply assembleResultProgram.of_eq
  intro q
  unfold assembleResult resultPart resultAt mapResult emitFree emitActive rowInput pairResults withRow
  cases ht : q.2.2.1 <;> cases hl : q.1.2.getD 0 none <;> cases hr : q.1.2.getD 1 none <;> rfl

private noncomputable def assemble (p : Policy) (f : Nat→Nat) (q : FuelState) (rs : List BlockResult) : BlockResult :=
  if q.1=0 then none else
    match UnitContextSelectionCode.selectCode q.2.1 with
    | none => (CurrentTreeInputCoverage.compile q.2.1 q.2.2).map (groundBlock p f)
    | some r => (selectedChild p (q,r)).bind fun k => resultPart ((q,rs),k)

private theorem assembleProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable₂ (assemble p f) := by
  have ctx : Primrec (fun q : AssemblyInput => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have a : Primrec (fun q : AssemblyInput => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hselect := UnitContextSelectionCode.StatementChecks.primitive_recursive_selection.comp ctx
  have hinput := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.2.comp ctx.to_comp a.to_comp
  have hbase : Computable (fun q : AssemblyInput => (CurrentTreeInputCoverage.compile q.1.2.1 q.1.2.2).map (groundBlock p f)) :=
    Computable.option_map hinput ((groundBlockProgram p hp f hc hf).comp Computable.snd).to₂
  let V := AssemblyInput×SelectedSplit
  have hstep := (selectedProgram p hp).comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd : Primrec fun q : V => q.2)).to_comp
  have ht : Computable (fun q : V => (selectedChild p (q.1.1,q.2)).bind fun k => resultPart (q.1,k)) :=
    Computable.option_bind hstep (resultPartProgram.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  have casesProgram := Computable.option_casesOn hselect.to_comp hbase ht.to₂
  have h := chooseProgram (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
    (Computable.const none) casesProgram
  have unary : Computable (fun q : AssemblyInput => assemble p f q.1 q.2) := by
    apply h.of_eq
    intro q
    by_cases hz : q.1.1 = 0
    · simp [assemble,hz]
    · cases hs : UnitContextSelectionCode.selectCode q.1.2.1 <;> simp [assemble,hz,hs]
  exact unary.to₂

private theorem calibration (p : Policy) (f : Nat→Nat) (q : FuelState) : blockFuel p f q.1 q.2.1 q.2.2 =
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
        cases hk : k.2.1 <;> simp [children,assemble,blockFuel,h,selectedChild,hp,tasks,hk,resultPart]

theorem blockFuelProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : Nat×List Nat×Nat => blockFuel p f q.1 q.2.1 q.2.2) :=
  (exactDecreasingGraph FuelState BlockResult (children p) (assemble p f) Prod.fst (childrenProgram p hp)
    (assembleProgram p hp f hc hf) Computable.fst _ (childDecrease p) (calibration p f)).2

theorem blockProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : List Nat×Nat => block p f q.1 q.2) :=
  (blockFuelProgram p hp f hc hf).comp ((Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)).pair Primrec.id).to_comp

theorem effectiveMatrixUnitCodes : Targets.EffectiveMatrixUnitCodes :=
  ⟨MatrixCode.renameTermProgram,MatrixCode.renameFormulaProgram,MatrixCode.inputCodeProgram,
    fun p hp f hc hf => ⟨blockFuelProgram p hp f hc hf,blockProgram p hp f hc hf⟩⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
