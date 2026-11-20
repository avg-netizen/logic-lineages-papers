module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphLayoutProgramsProof

@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.TailPrograms
open MatrixCode (varProgram litProgram addProgram)

abbrev Input := Nat×Nat×Nat×Nat×List Nat×Nat
private abbrev Tail := Input

private def rows (q : Tail) : List Nat :=
  let w := q.1
  let d := q.2.1
  let t := directWidth w d
  [MatrixCode.le (MatrixCode.lit (max q.2.2.1 q.2.2.2.1)) (MatrixCode.var t),
   MatrixCode.eq (MatrixCode.var (uSlot w 0)) (MatrixCode.var t),
   MatrixCode.eq (MatrixCode.var (w+2)) (MatrixCode.lit 0),
   MatrixCode.eq (MatrixCode.var (uSlot w d))
     (MatrixCode.add (MatrixCode.lit q.2.2.2.1) (MatrixCode.var (w+1))),
   q.2.2.2.2.2,
   MatrixCode.eq (MatrixCode.var (t+1))
     (MatrixCode.add (MatrixCode.var w) (MatrixCode.lit (d+1)))]

private def gateAt (q : Tail) (j : Nat) : Nat :=
  fGate rawLayout q.2.2.2.2.1 (uSlot q.1 j) (uSlot q.1 (j+1)) (argSlot q.1 q.2.1 j)

section
attribute [local irreducible] MatrixCode.eq MatrixCode.le MatrixCode.both
  MatrixCode.var MatrixCode.lit MatrixCode.add directWidth uSlot argSlot fGate

private theorem rowsProgram : Primrec rows := by
  have w : Primrec (fun q : Tail => q.1) := Primrec.fst
  have d : Primrec (fun q : Tail => q.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun q : Tail => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have b : Primrec (fun q : Tail => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have small : Primrec (fun q : Tail => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have ray : Primrec (fun q : Tail => q.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have t := widthProgram.comp w d
  have i0 := leProgram.comp (litProgram.comp (Primrec.nat_max.comp n b)) (varProgram.comp t)
  have u0 := uProgram.comp w (Primrec.const 0)
  have ud := uProgram.comp w d
  have i1 := eqProgram.comp (varProgram.comp u0) (varProgram.comp t)
  have i2 := eqProgram.comp (varProgram.comp (Primrec.nat_add.comp w (Primrec.const 2))) (Primrec.const (MatrixCode.lit 0))
  have i3 := eqProgram.comp (varProgram.comp ud)
    (addProgram.comp (litProgram.comp b) (varProgram.comp (Primrec.succ.comp w)))
  have i5 := eqProgram.comp (varProgram.comp (Primrec.succ.comp t))
    (addProgram.comp (varProgram.comp w) (litProgram.comp (Primrec.succ.comp d)))
  have code := Primrec.list_cons.comp i0 (Primrec.list_cons.comp i1 (Primrec.list_cons.comp i2
    (Primrec.list_cons.comp i3 (Primrec.list_cons.comp ray (MatrixCode.singleProgram i5)))))
  unfold rows
  exact code

private theorem gateAtProgram : Primrec₂ gateAt := by
  have w : Primrec (fun q : Tail => q.1) := Primrec.fst
  have d : Primrec (fun q : Tail => q.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun q : Tail => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have b : Primrec (fun q : Tail => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have small : Primrec (fun q : Tail => q.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have ray : Primrec (fun q : Tail => q.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  let P := Tail×Nat
  have idx : Primrec (fun q : P => q.2) := Primrec.snd
  have uw := uProgram.comp (w.comp Primrec.fst) idx
  have uw' := uProgram.comp (w.comp Primrec.fst) (Primrec.succ.comp idx)
  have ax := argProgram.comp ((w.comp Primrec.fst).pair ((d.comp Primrec.fst).pair idx))
  have gate := gateProgram.comp ((small.comp Primrec.fst).pair (uw.pair (uw'.pair ax)))
  unfold gateAt
  exact gate.to₂
end

private theorem conjunctionProgram : Primrec (fun xs : List Nat => xs.foldr MatrixCode.both 0) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (andProgram.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem tailProgram : Primrec (fun q : Input => tailBody rawLayout q.1 q.2.1 q.2.2.1
    q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  have d : Primrec (fun q : Input => q.2.1) := Primrec.fst.comp Primrec.snd
  have gates := Primrec.list_map (Primrec.list_range.comp d) gateAtProgram
  exact (conjunctionProgram.comp (Primrec.list_append.comp rowsProgram gates)).of_eq
    (fun q => by rfl)

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.TailPrograms
