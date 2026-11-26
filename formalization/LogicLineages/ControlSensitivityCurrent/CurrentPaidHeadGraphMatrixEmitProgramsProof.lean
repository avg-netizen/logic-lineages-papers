module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixRenameProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionCodePrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode

open LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof (exactDecreasingGraph)
open CurrentGroundAnnotationPrograms (chooseProgram)
open RawSourceDAG.InputCompiler (InputStep)

private abbrev E := Nat×Nat
private abbrev Task := E×List Emit

private theorem noneRow (k : Nat) : Primrec₂ (noneStep k) :=
  ((Primrec.const k).pair Primrec.id).pair (Primrec.const none)
private theorem sourceRow (k j : Nat) : Primrec (sourceStep k j) :=
  (Primrec.const (k,j,0)).pair Primrec.option_some
private theorem portLift : Primrec₂ liftPort :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.snd Primrec.fst)

private def splitTasks (width : Nat→Nat) (q : E) : List E :=
  let p := (q.2/8).unpair
  [(q.1,p.1),(q.1+width p.1,p.2)]

private theorem splitProgram {width : Nat→Nat} (hw : Computable width) : Computable (splitTasks width) := by
  have l := leftProgram.to_comp.comp (Computable.snd : Computable fun q : E => q.2)
  have r := rightProgram.to_comp.comp (Computable.snd : Computable fun q : E => q.2)
  have a := (Computable.fst : Computable fun q : E => q.1).pair l
  have b := (Primrec.nat_add.to_comp.comp Computable.fst (hw.comp l)).pair r
  exact Primrec.list_cons.to_comp.comp a (Primrec.list_cons.to_comp.comp b (Computable.const []))

private def termTasks (q : E) : List E :=
  if q.2%8=2 then splitTasks termWidth q
  else if q.2%8=4 then [(q.1,(q.2/8).unpair.2)] else []
private theorem termTasksProgram : Computable termTasks :=
  chooseProgram ((isTag 2).comp Primrec.snd) (splitProgram termWidthProgram)
    (chooseProgram ((isTag 4).comp Primrec.snd)
      (singleProgram (Primrec.fst.pair (rightProgram.comp Primrec.snd))).to_comp (Computable.const []))

private def formTasks (q : E) : List E :=
  if 5≤q.2%8 then if q.2%8=5 then [(q.1,q.2/8)] else splitTasks formulaWidth q else []
private theorem formTasksProgram : Computable formTasks :=
  chooseProgram (clusteredTag.comp Primrec.snd) (chooseProgram ((isTag 5).comp Primrec.snd)
    (singleProgram (Primrec.fst.pair (digitProgram.comp Primrec.snd))).to_comp (splitProgram formulaWidthProgram))
    (Computable.const [])

private theorem termDecreases (q z : E) (hz : z∈termTasks q) : z.2<q.2 := by
  apply termChildDecrease q.2 z.2
  change z.2 ∈ childTerm q.2
  unfold termTasks at hz
  by_cases h2 : q.2%8=2
  · simp only [h2,if_true,splitTasks,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl <;> simp [childTerm,h2]
  · by_cases h4 : q.2%8=4
    · simp only [h4,Nat.reduceEqDiff,if_false,if_true,List.mem_singleton] at hz
      subst z
      simp [childTerm,h2,h4]
    · simp [h2,h4] at hz

private theorem formDecreases (q z : E) (hz : z∈formTasks q) : z.2<q.2 := by
  apply formulaChildDecrease q.2 z.2
  unfold formTasks at hz
  by_cases h : 5≤q.2%8
  · by_cases h5 : q.2%8=5
    · simp only [h5,le_refl,if_true,List.mem_singleton] at hz
      subst z
      simp [childFormula,h,h5]
    · simp only [h,h5,if_true,if_false,splitTasks,List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl <;> simp [childFormula,h,h5]
  · simp [h] at hz

private def blankEmit : Emit := ([],0,0)
private def nth (i : Nat) (rs : List Emit) : Emit := rs.getD i blankEmit
private theorem nthProgram (i : Nat) : Primrec (nth i) := (Primrec.list_getD blankEmit).comp Primrec.id (Primrec.const i)

private def addOutput (l r : Emit) : Emit :=
  (l.1++r.1++[noneStep 6 (liftPort r.2.1 l.2.2) r.2.2],l.2.1+r.2.1+1,1)
private theorem addOutputProgram : Primrec₂ addOutput := by
  let D := Emit×Emit
  have l : Primrec (fun q : D => q.1) := Primrec.fst
  have r : Primrec (fun q : D => q.2) := Primrec.snd
  have ld := Primrec.fst.comp (Primrec.snd.comp l)
  have rd := Primrec.fst.comp (Primrec.snd.comp r)
  have lv := Primrec.snd.comp (Primrec.snd.comp l)
  have rv := Primrec.snd.comp (Primrec.snd.comp r)
  have rows := Primrec.list_append.comp (Primrec.fst.comp l) (Primrec.fst.comp r)
  have a := (noneRow 6).comp (portLift.comp rd lv) rv
  exact (Primrec.list_append.comp rows (singleProgram a)).pair
    ((Primrec.nat_add.comp (Primrec.nat_add.comp ld rd) (Primrec.const 1)).pair (Primrec.const 1))

private def unaryOutput (code : Nat) (a : Emit) : Emit :=
  (a.1++[noneStep 6 a.2.2 0,sourceStep 9 0 (payload (code/8).unpair.1)],a.2.1+2,1)
private theorem unaryOutputProgram : Primrec₂ unaryOutput := by
  let D := Nat×Emit
  have a : Primrec (fun q : D => q.2) := Primrec.snd
  have r := (noneRow 6).comp (Primrec.snd.comp (Primrec.snd.comp a)) (Primrec.const 0)
  have c : Primrec (fun q : D => q.1) := Primrec.fst
  have s := (sourceRow 9 0).comp (payloadProgram.comp (leftProgram.comp c))
  exact (Primrec.list_append.comp (Primrec.fst.comp a) (pairListProgram r s)).pair
    ((Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp a)) (Primrec.const 2)).pair (Primrec.const 1))

private def termAssemble (q : E) (rs : List Emit) : Emit :=
  let k := q.2%8
  let n := q.2/8
  if k=0 then ([],0,n+q.1+1)
  else if k=2 then addOutput (nth 0 rs) (nth 1 rs)
  else if k=4 then unaryOutput q.2 (nth 0 rs)
  else if k=3 then ([sourceStep 8 0 (CurrentDecisionEmitter.liftCode q.1 (payload n))],1,1)
  else ([noneStep 7 n 0],1,1)

private theorem termAssembleProgram : Primrec₂ termAssemble := by
  have f : Primrec (fun q : Task => q.1.1) := Primrec.fst.comp Primrec.fst
  have c : Primrec (fun q : Task => q.1.2) := Primrec.snd.comp Primrec.fst
  have n := digitProgram.comp c
  have v (i : Nat) := (nthProgram i).comp (Primrec.snd : Primrec (fun q : Task => q.2))
  have a := (sourceRow 8 0).comp (CurrentDecision.liftCodePrimitive.comp f (payloadProgram.comp n))
  have b := (noneRow 7).comp n (Primrec.const 0)
  exact Primrec.ite ((isTag 0).comp c) ((Primrec.const []).pair ((Primrec.const 0).pair
      (Primrec.nat_add.comp (Primrec.nat_add.comp n f) (Primrec.const 1))))
    (Primrec.ite ((isTag 2).comp c) (addOutputProgram.comp (v 0) (v 1))
      (Primrec.ite ((isTag 4).comp c) (unaryOutputProgram.comp c (v 0))
        (Primrec.ite ((isTag 3).comp c) ((singleProgram a).pair (Primrec.const (1,1)))
          ((singleProgram b).pair (Primrec.const (1,1))))))

private theorem termAssemblerCal (q : E) : emitTerm q.1 q.2 = termAssemble q
    ((termTasks q).map (fun q => emitTerm q.1 q.2)) := by
  rw [emitTerm]
  by_cases h0 : q.2%8=0 <;> by_cases h2 : q.2%8=2 <;> by_cases h4 : q.2%8=4 <;>
    by_cases h3 : q.2%8=3 <;> simp [termTasks,termAssemble,splitTasks,nth,h0,h2,h4,h3,
      addOutput,unaryOutput,exactTermWidth]

theorem emitTermProgram : Computable₂ emitTerm :=
  (exactDecreasingGraph E Emit termTasks termAssemble Prod.snd termTasksProgram termAssembleProgram.to_comp
    Computable.snd _ termDecreases termAssemblerCal).2

private def boolNot (a : Emit) : Emit := (a.1++[noneStep 3 0 0],a.2.1,a.2.2+1)
private def boolJoin (tag : Nat) (l r : Emit) : Emit :=
  (l.1++r.1++[noneStep (tag-2) r.2.2 0],l.2.1+r.2.1,l.2.2+r.2.2+1)
private def boolRelation (tag : Nat) (l r : Emit) : Emit :=
  (l.1++r.1++[noneStep (tag-2) (liftPort r.2.1 l.2.2) r.2.2],l.2.1+r.2.1,1)
private def boolUnit (tag : Nat) : Emit := ([noneStep (if tag=0 then 0 else 2) 0 0],0,1)

private theorem boolNotProgram : Primrec boolNot := by
  exact (Primrec.list_append.comp Primrec.fst (Primrec.const _)).pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))

private theorem boolJoinProgram : Primrec (fun q : Nat×Emit×Emit => boolJoin q.1 q.2.1 q.2.2) := by
  let P := Nat×Emit×Emit
  have l : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun q : P => q.2.2) := Primrec.snd.comp Primrec.snd
  have t : Primrec (fun q : P => q.1-2) := Primrec.nat_sub.comp Primrec.fst (Primrec.const 2)
  have b : Primrec (fun q : P => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp r)
  have br : Primrec (fun q : P => noneStep (q.1-2) q.2.2.2.2 0) :=
    ((t.pair (b.pair (Primrec.const 0))).pair (Primrec.const none))
  have w := Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp l)) (Primrec.fst.comp (Primrec.snd.comp r))
  have j := Primrec.succ.comp (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp l)) b)
  exact (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.fst.comp l) (Primrec.fst.comp r))
    (singleProgram br)).pair (w.pair j)

private theorem boolRelationProgram : Primrec (fun q : Nat×Emit×Emit => boolRelation q.1 q.2.1 q.2.2) := by
  let P := Nat×Emit×Emit
  have l : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have r : Primrec (fun q : P => q.2.2) := Primrec.snd.comp Primrec.snd
  have t : Primrec (fun q : P => q.1-2) := Primrec.nat_sub.comp Primrec.fst (Primrec.const 2)
  have a := portLift.comp (Primrec.fst.comp (Primrec.snd.comp r)) (Primrec.snd.comp (Primrec.snd.comp l))
  have b := Primrec.snd.comp (Primrec.snd.comp r)
  have br : Primrec (fun q : P => noneStep (q.1-2) (liftPort q.2.2.2.1 q.2.1.2.2) q.2.2.2.2) :=
    (t.pair (a.pair b)).pair (Primrec.const none)
  have w := Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp l)) (Primrec.fst.comp (Primrec.snd.comp r))
  exact (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.fst.comp l) (Primrec.fst.comp r))
    (singleProgram br)).pair (w.pair (Primrec.const 1))

private theorem boolUnitProgram : Primrec boolUnit := by
  have h : Primrec (fun j : Nat => if j=0 then (([noneStep 0 0 0],0,1) : Emit)
      else ([noneStep 2 0 0],0,1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const _) (Primrec.const _)
  exact h.of_eq (fun j => by by_cases hj : j=0 <;> simp only [boolUnit,hj,if_true,if_false])

private def formAssemble (q : E) (rs : List Emit) : Emit :=
  let k := q.2%8
  if 5≤k then
    if k=5 then boolNot (nth 0 rs) else boolJoin k (nth 0 rs) (nth 1 rs)
  else if 2≤k then
    let a := emitTerm q.1 (q.2/8).unpair.1
    let b := emitTerm (q.1+a.2.1) (q.2/8).unpair.2
    boolRelation k a b
  else boolUnit k

private theorem formAssembleProgram : Computable₂ formAssemble := by
  have f : Primrec (fun q : Task => q.1.1) := Primrec.fst.comp Primrec.fst
  have c : Primrec (fun q : Task => q.1.2) := Primrec.snd.comp Primrec.fst
  have k := tagProgram.comp c
  have v (i : Nat) := (nthProgram i).comp (Primrec.snd : Primrec fun q : Task => q.2)
  have a := emitTermProgram.comp f.to_comp (leftProgram.comp c).to_comp
  have off := Primrec.nat_add.to_comp.comp f.to_comp (Computable.fst.comp (Computable.snd.comp a))
  have b := emitTermProgram.comp off (rightProgram.comp c).to_comp
  exact chooseProgram (clusteredTag.comp c) (chooseProgram ((isTag 5).comp c)
    (boolNotProgram.comp (v 0)).to_comp (boolJoinProgram.comp (k.pair ((v 0).pair (v 1)))).to_comp)
    (chooseProgram (Primrec.nat_le.comp (Primrec.const 2) k)
      (boolRelationProgram.to_comp.comp (k.to_comp.pair (a.pair b))) (boolUnitProgram.comp k).to_comp)

private theorem formAssemblerCal (q : E) : emitFormula q.1 q.2 = formAssemble q
    ((formTasks q).map (fun q => emitFormula q.1 q.2)) := by
  rw [emitFormula]
  by_cases h : 5≤q.2%8 <;> by_cases h5 : q.2%8=5 <;> by_cases h2 : 2≤q.2%8 <;>
    simp [h,h5,h2,formTasks,formAssemble,splitTasks,exactFormulaWidth,nth,boolNot,boolJoin,boolRelation,boolUnit]

theorem emitFormulaProgram : Computable₂ emitFormula :=
  (exactDecreasingGraph E Emit formTasks formAssemble Prod.snd formTasksProgram formAssembleProgram
    Computable.snd _ formDecreases formAssemblerCal).2

theorem inputCodeProgram : Computable inputCode :=
  (Computable.fst.comp (emitFormulaProgram.comp (Computable.const 0) Computable.id)).pair (Computable.const 0)

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.MatrixCode
