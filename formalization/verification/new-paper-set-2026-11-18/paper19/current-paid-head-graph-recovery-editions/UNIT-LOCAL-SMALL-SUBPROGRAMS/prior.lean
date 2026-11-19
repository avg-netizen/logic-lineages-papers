module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixEmitProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum CurrentOneUnit
open RawSourceDAG (Code)
open MatrixCode

private theorem binaryNode (t : Nat) : Primrec₂ (MatrixCode.atom t) :=
  atomProgram.comp ((Primrec.const t).pair Primrec.id)

theorem rawProgram : Primrec MatrixCode.raw := addProgram.comp varProgram (Primrec.const (lit 1))
private theorem timesProgram : Primrec₂ MatrixCode.times := by
  let S := Nat×Nat×Nat
  have a : Primrec (fun q : S => q.1) := Primrec.fst
  have x : Primrec (fun q : S => q.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec₂ (fun a (q : Nat×Nat) => MatrixCode.add a q.2) :=
    (addProgram.comp a x).to₂
  have recurse := Primrec.nat_rec (Primrec.const (lit 0) : Primrec (fun _ : Nat => lit 0)) step
  exact recurse.comp Primrec.snd Primrec.fst

theorem rowProgram : Primrec (fun q : LinearCode×Nat×Nat×Nat => rawRow q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  let P := LinearCode×Nat×Nat×Nat
  have row : Primrec (fun q : P => q.1) := Primrec.fst
  have b : Primrec (fun q : P => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp row)
  have c : Primrec (fun q : P => q.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp row))
  have d : Primrec (fun q : P => q.1.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp row)))
  have e : Primrec (fun q : P => q.1.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp row)))
  have l : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have m : Primrec (fun q : P => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have r : Primrec (fun q : P => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have left : Primrec (fun q : P => add (times q.1.1 q.2.1) (lit q.1.2.1)) :=
    addProgram.comp (timesProgram.comp (Primrec.fst.comp row) l) (litProgram.comp b)
  have middle : Primrec (fun q : P => add (times q.1.2.2.1 q.2.2.1)
      (times q.1.2.2.2.1 q.2.2.2)) := addProgram.comp (timesProgram.comp c m) (timesProgram.comp d r)
  have right : Primrec (fun q : P => add (add (times q.1.2.2.1 q.2.2.1)
      (times q.1.2.2.2.1 q.2.2.2)) (lit q.1.2.2.2.2)) := addProgram.comp middle (litProgram.comp e)
  exact (binaryNode 2).comp left right

private theorem eraserShiftProgram : Primrec shiftEraser := by
  have g : Primrec (fun q : Code => q.1) := Primrec.fst
  have l : Primrec (fun q : Code => q.1.length-2) := Primrec.nat_sub.comp (Primrec.list_length.comp g) (Primrec.const 2)
  have t : Primrec (fun q : Code => (List.range (q.1.length-2)).map (fun i => i+3)) :=
    Primrec.list_map (Primrec.list_range.comp l)
      (Primrec.nat_add.comp (Primrec.snd : Primrec (fun q : Code×Nat => q.2)) (Primrec.const 3)).to₂
  have table : Primrec (fun q : Code => 0::1::(List.range (q.1.length-2)).map (fun i => i+3)) :=
    Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 1) t)
  exact RawSourceDAG.Operations.rename_code_primitive.comp
    ((Primrec.list_cons.comp (Primrec.const 0) g).pair (table.pair Primrec.id))
private theorem originalProgram : Primrec originalEraser :=
  eraserShiftProgram.comp (CurrentProbeCode.effective.2.comp
    (CurrentDecision.liftCodePrimitive.comp (Primrec.const 2) Primrec.id) (Primrec.const 0))
private theorem closedProgram : Primrec closedEraser := by
  have g : Primrec (fun q : Code => 0::0::q.1) := Primrec.list_append.comp (Primrec.const [0,0]) Primrec.fst
  have args : Primrec (fun q : Code => (0::0::q.1,([] : List Nat),CurrentProbeCode.closeRaw q)) :=
    g.pair ((Primrec.const []).pair CurrentProbeCode.effective.1)
  have r := RawSourceDAG.Operations.rename_code_primitive.comp args
  exact eraserShiftProgram.comp (CurrentProbeCode.effective.2.comp r (Primrec.const 1))

private def groundOutput (q : Code×Nat) : Block :=
  let d := 2*(SyntaxCode.typeLevel q.1.2.2.2+1)+1
  (2,both (eq (observe (originalEraser q.1)) (observe (closedEraser q.1)))
    (eq (add (times d (MatrixCode.raw 2)) (MatrixCode.raw 0))
      (add (lit (d*q.2)) (MatrixCode.raw 1))))

private theorem groundOutputProgram : Primrec groundOutput := by
  let P := Code×Nat
  have v : Primrec (fun q : P => q.1) := Primrec.fst
  have d : Primrec (fun q : P => CurrentDecision.factorCode q.1) :=
    CurrentDecision.factorCodePrimitive.comp v
  have l := (binaryNode 2).comp (observeProgram.comp (originalProgram.comp v)) (observeProgram.comp (closedProgram.comp v))
  have a := addProgram.comp (timesProgram.comp d (Primrec.const (MatrixCode.raw 2)))
    (Primrec.const (MatrixCode.raw 0))
  have b := addProgram.comp (litProgram.comp (Primrec.nat_mul.comp d Primrec.snd)) (Primrec.const (MatrixCode.raw 1))
  exact (Primrec.const 2).pair ((binaryNode 6).comp l ((binaryNode 2).comp a b))

section
attribute [local irreducible] groundOutput CurrentAbsolute.anchor groundBlock
theorem groundBlockProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat→Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) : Computable (groundBlock p f) := by
  have C : Computable (CurrentAbsolute.anchor p f) := CurrentAbsolute.anchorEffective p hp f hc hf
  have pack : Computable (fun d : Code => (d,CurrentAbsolute.anchor p f d)) :=
    (Computable.id : Computable (id : Code→Code)).pair C
  have H : Computable (fun d : Code => groundOutput (d,CurrentAbsolute.anchor p f d)) :=
    groundOutputProgram.to_comp.comp pack
  exact H.of_eq (fun d => by unfold groundOutput groundBlock; rfl)
end

private theorem renamePart {P : Type} [Primcodable P] {g t : P→List Nat} {n : P→Nat}
    (hg : Primrec g) (ht : Primrec t) (hn : Primrec n) :
    Computable (fun q => MatrixCode.renameFormula (g q) (t q) (n q)) :=
  renameFormulaProgram.comp (hg.pair (ht.pair hn)).to_comp

theorem freeBlockProgram : Computable (fun q : Nat×LinearCode×Block => freeBlock q.1 q.2.1 q.2.2) := by
  let P := Nat×LinearCode×Block
  have g : Primrec (fun q : P => q.1) := Primrec.fst
  have row : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have b : Primrec (fun q : P => q.2.2) := Primrec.snd.comp Primrec.snd
  have w := Primrec.fst.comp b
  have w' := Primrec.succ.comp w
  have length := Primrec.nat_add.comp w' g
  have ctx := replicateZero.comp (Primrec.nat_add.comp (Primrec.succ.comp w') g)
  have idx : Primrec (fun q : P×Nat => if q.2=q.1.2.2.1 then 0 else q.2+1) :=
    Primrec.ite (Primrec.eq.comp Primrec.snd (w.comp Primrec.fst)) (Primrec.const 0) (Primrec.succ.comp Primrec.snd)
  have table := Primrec.list_map (Primrec.list_range.comp length) idx.to₂
  have a := renamePart ctx table (Primrec.snd.comp b)
  have r := rowProgram.comp (row.pair ((Primrec.const (MatrixCode.raw 0)).pair
    ((Primrec.const (lit 0)).pair (rawProgram.comp w'))))
  exact w'.to_comp.pair ((binaryNode 6).to_comp.comp a r.to_comp)

/-- Exact active frame components are checked independently so the final
packing proof need not unfold the recursive renamer to infer any type. -/
private abbrev ActiveArgs := Nat×LinearCode×Block×Block

private def activeW (q : ActiveArgs) := q.2.2.1.1+q.2.2.2.1+2
private theorem activeLeftWidth : Primrec (fun q : ActiveArgs => q.2.2.1.1) :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem activeRightWidth : Primrec (fun q : ActiveArgs => q.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem activeWProgram : Primrec activeW :=
  Primrec.nat_add.comp (Primrec.nat_add.comp activeLeftWidth activeRightWidth) (Primrec.const 2)

private def activeCtx (q : ActiveArgs) := bitCtx (activeW q+1+q.1)
private theorem activeCtxProgram : Primrec activeCtx :=
  replicateZero.comp (Primrec.nat_add.comp (Primrec.succ.comp activeWProgram) Primrec.fst)

private def activeLIndex (q : ActiveArgs) (i : Nat) : Nat :=
  if i<q.2.2.1.1 then i+2 else if i=q.2.2.1.1 then 0 else i+q.2.2.2.1+2
private def activeRIndex (q : ActiveArgs) (i : Nat) : Nat :=
  if i=q.2.2.2.1 then 1 else i+q.2.2.1.1+2

private theorem activeOffset {h : ActiveArgs→Nat} (hh : Primrec h) :
    Primrec (fun q : ActiveArgs×Nat => q.2+h q.1+2) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd (hh.comp Primrec.fst)) (Primrec.const 2)

private theorem activeLIndexProgram : Primrec₂ activeLIndex := by
  let P := ActiveArgs×Nat
  have i : Primrec (fun q : P => q.2) := Primrec.snd
  have a : Primrec (fun q : P => q.1.2.2.1.1) := activeLeftWidth.comp Primrec.fst
  exact Primrec.ite (Primrec.nat_lt.comp i a) (Primrec.nat_add.comp i (Primrec.const 2))
    (Primrec.ite (Primrec.eq.comp i a) (Primrec.const 0) (activeOffset activeRightWidth))

private theorem activeRIndexProgram : Primrec₂ activeRIndex := by
  let P := ActiveArgs×Nat
  have i : Primrec (fun q : P => q.2) := Primrec.snd
  have b : Primrec (fun q : P => q.1.2.2.2.1) := activeRightWidth.comp Primrec.fst
  exact Primrec.ite (Primrec.eq.comp i b) (Primrec.const 1) (activeOffset activeLeftWidth)

private theorem activeRange {h : ActiveArgs→Nat} (hh : Primrec h) :
    Primrec (fun q => List.range (h q+1+q.1)) :=
  Primrec.list_range.comp (Primrec.nat_add.comp (Primrec.succ.comp hh) Primrec.fst)

private def activeLeft (q : ActiveArgs) : Nat :=
  MatrixCode.renameFormula (activeCtx q)
    ((List.range (q.2.2.1.1+1+q.1)).map (activeLIndex q)) q.2.2.1.2
private def activeRight (q : ActiveArgs) : Nat :=
  MatrixCode.renameFormula (activeCtx q)
    ((List.range (q.2.2.2.1+1+q.1)).map (activeRIndex q)) q.2.2.2.2

private theorem activeLeftProgram : Computable activeLeft := by
  have src : Primrec (fun q : ActiveArgs => q.2.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have table : Primrec (fun q : ActiveArgs => (List.range (q.2.2.1.1+1+q.1)).map (activeLIndex q)) :=
    Primrec.list_map (activeRange activeLeftWidth) activeLIndexProgram
  exact renamePart activeCtxProgram table src

private theorem activeRightProgram : Computable activeRight := by
  have src : Primrec (fun q : ActiveArgs => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have table : Primrec (fun q : ActiveArgs => (List.range (q.2.2.2.1+1+q.1)).map (activeRIndex q)) :=
    Primrec.list_map (activeRange activeRightWidth) activeRIndexProgram
  exact renamePart activeCtxProgram table src

private def activeRow (q : ActiveArgs) : Nat :=
  rawRow q.2.1 (MatrixCode.raw 0) (MatrixCode.raw 1) (MatrixCode.raw (activeW q))
private theorem activeRowProgram : Primrec activeRow := by
  have row : Primrec (fun q : ActiveArgs => q.2.1) := Primrec.fst.comp Primrec.snd
  have z : Primrec (fun _ : ActiveArgs => MatrixCode.raw 0) := Primrec.const _
  have o : Primrec (fun _ : ActiveArgs => MatrixCode.raw 1) := Primrec.const _
  have w : Primrec (fun q : ActiveArgs => MatrixCode.raw (activeW q)) := rawProgram.comp activeWProgram
  exact rowProgram.comp (row.pair (z.pair (o.pair w)))

private def activeOutput (q : ActiveArgs) : Block :=
  (activeW q,MatrixCode.both (MatrixCode.both (activeLeft q) (activeRight q)) (activeRow q))

section
attribute [local irreducible] activeLeft activeRight activeRow activeW activeOutput
private theorem activeOutputProgram : Computable activeOutput := by
  have inner : Computable (fun q : ActiveArgs => MatrixCode.both (activeLeft q) (activeRight q)) :=
    (binaryNode 6).to_comp.comp activeLeftProgram activeRightProgram
  have outer : Computable (fun q : ActiveArgs =>
      MatrixCode.both (MatrixCode.both (activeLeft q) (activeRight q)) (activeRow q)) :=
    (binaryNode 6).to_comp.comp inner activeRowProgram.to_comp
  unfold activeOutput
  exact activeWProgram.to_comp.pair outer

theorem activeBlockProgram : Computable (fun q : Nat×LinearCode×Block×Block => activeBlock q.1 q.2.1 q.2.2.1 q.2.2.2) :=
  activeOutputProgram.of_eq (fun q => by
    unfold activeOutput activeLeft activeRight activeCtx activeLIndex activeRIndex activeRow activeW activeBlock
    rfl)
end

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.UnitCode
