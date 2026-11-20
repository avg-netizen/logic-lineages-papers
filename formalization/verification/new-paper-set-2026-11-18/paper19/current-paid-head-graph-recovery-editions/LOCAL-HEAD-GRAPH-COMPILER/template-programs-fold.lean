module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphLayoutProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitLocalProgramsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open MatrixCode (addProgram litProgram varProgram renameFormulaProgram)
open UnitCode (Block)

private abbrev Tail := Nat×Nat×Nat×Nat×List Nat×Nat
private abbrev D := Nat×Nat×Nat×Nat×List Nat×List Nat×Nat

section
attribute [local irreducible] MatrixCode.eq MatrixCode.le MatrixCode.both MatrixCode.either
  MatrixCode.var MatrixCode.lit MatrixCode.add directWidth uSlot argSlot fGate

private theorem tailProgram : Primrec (fun q : Tail => tailBody rawLayout q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
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
  have rows := Primrec.list_cons.comp i0 (Primrec.list_cons.comp i1 (Primrec.list_cons.comp i2
    (Primrec.list_cons.comp i3 (Primrec.list_cons.comp ray (MatrixCode.singleProgram i5)))))
  let P := Tail×Nat
  have idx : Primrec (fun q : P => q.2) := Primrec.snd
  have uw := uProgram.comp (w.comp Primrec.fst) idx
  have uw' := uProgram.comp (w.comp Primrec.fst) (Primrec.succ.comp idx)
  have ax := argProgram.comp ((w.comp Primrec.fst).pair ((d.comp Primrec.fst).pair idx))
  have gate := gateProgram.comp ((small.comp Primrec.fst).pair (uw.pair (uw'.pair ax)))
  have gates := Primrec.list_map (Primrec.list_range.comp d) gate.to₂
  unfold tailBody
  exact Primrec.list_foldr (Primrec.list_append.comp rows gates) (Primrec.const 0)
    (andProgram.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

attribute [local irreducible] tailBody

private theorem directBodyProgram : Primrec (fun q : D => directBody rawLayout q.1 q.2.1 q.2.2.1
    q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  have a : Primrec (fun q : D => q.1) := Primrec.fst
  have d : Primrec (fun q : D => q.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun q : D => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have base : Primrec (fun q : D => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tail : Primrec (fun q : D => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have small : Primrec (fun q : D => q.2.2.2.2.1) := Primrec.fst.comp tail
  have points : Primrec (fun q : D => q.2.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp tail)
  have ray : Primrec (fun q : D => q.2.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp tail)
  have w := widthProgram.comp a d
  unfold directBody
  exact orProgram.comp (prefixProgram.comp ((w.pair (Primrec.succ.comp w)).pair (n.pair points)))
    (tailProgram.comp (a.pair (d.pair (n.pair (base.pair (small.pair ray))))))

attribute [local irreducible] directBody rayPlacement

private abbrev DirectIn := Nat×Block×Nat×Nat×Nat×List Nat×List Nat

theorem directBlockProgram : Computable (fun q : Nat×Block×Nat×Nat×Nat×List Nat×List Nat => directBlock q.1 q.2.1 q.2.2.1 q.2.2.2.1
    q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  let P := DirectIn
  have g : Primrec (fun q : P => q.1) := Primrec.fst
  have r : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have d : Primrec (fun q : P => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have n : Primrec (fun q : P => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have p : Primrec (fun q : P => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have wr := Primrec.fst.comp r
  have wi := widthProgram.comp wr d
  have ctx := replicateZero.comp (Primrec.nat_add.comp wi (Primrec.const 2))
  have len := Primrec.nat_add.comp (Primrec.nat_add.comp wr (Primrec.const 2)) g
  let Y := P×Nat
  have ix : Primrec (fun q : Y => q.2) := Primrec.snd
  have w := wr.comp (Primrec.fst : Primrec (fun q : Y => q.1))
  have rk : Primrec (fun q : Y => rayPlacement q.1.2.1.1 q.2) :=
    by
      unfold rayPlacement
      exact Primrec.ite (Primrec.nat_le.comp ix (Primrec.succ.comp w)) ix (Primrec.nat_add.comp w (Primrec.const 2))
  have tab := Primrec.list_map (Primrec.list_range.comp len) rk.to₂
  have rr := renameFormulaProgram.comp (ctx.pair (tab.pair (Primrec.snd.comp r))).to_comp
  have arg := wr.to_comp.pair (d.to_comp.pair (n.to_comp.pair
    ((Primrec.fst.comp p).to_comp.pair ((Primrec.fst.comp (Primrec.snd.comp p)).to_comp.pair
      ((Primrec.snd.comp (Primrec.snd.comp p)).to_comp.pair rr)))))
  unfold directBlock
  exact wi.to_comp.pair (directBodyProgram.to_comp.comp arg)
end

private abbrev I := Nat×Nat×Nat×Block×Block×Block

theorem insertedBlockProgram : Computable (fun q : Nat×Nat×Nat×Block×Block×Block =>
    insertedBlock q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  have g : Primrec (fun q : I => q.1) := Primrec.fst
  have n : Primrec (fun q : I => q.2.1) := Primrec.fst.comp Primrec.snd
  have lv : Primrec (fun q : I => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ps : Primrec (fun q : I => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have B : Primrec (fun q : I => q.2.2.2.1) := Primrec.fst.comp ps
  have C : Primrec (fun q : I => q.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp ps)
  have G : Primrec (fun q : I => q.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp ps)
  have a := Primrec.fst.comp B
  have b := Primrec.fst.comp C
  have c := Primrec.fst.comp G
  have e := Primrec.nat_add.comp (Primrec.nat_add.comp a b) c
  have w := Primrec.nat_add.comp e (Primrec.const 3)
  have ctx := replicateZero.comp (Primrec.nat_add.comp (Primrec.succ.comp w) g)
  let P := I×Nat
  have i : Primrec (fun q : P => q.2) := Primrec.snd
  have A := a.comp (Primrec.fst : Primrec (fun q : P => q.1))
  have B' := b.comp (Primrec.fst : Primrec (fun q : P => q.1))
  have C' := c.comp (Primrec.fst : Primrec (fun q : P => q.1))
  have E := e.comp (Primrec.fst : Primrec (fun q : P => q.1))
  have W := w.comp (Primrec.fst : Primrec (fun q : P => q.1))
  have ixB : Primrec (fun q : P => placeB q.1.2.2.2.1.1 q.1.2.2.2.2.1.1 q.1.2.2.2.2.2.1 q.2) :=
    Primrec.ite (Primrec.nat_lt.comp i A) i (Primrec.ite (Primrec.eq.comp i A) E
      (Primrec.nat_add.comp W (Primrec.nat_sub.comp i A)))
  have ixC : Primrec (fun q : P => placeC q.1.2.2.2.1.1 q.1.2.2.2.2.1.1 q.1.2.2.2.2.2.1 q.2) :=
    Primrec.ite (Primrec.nat_lt.comp i B') (Primrec.nat_add.comp A i)
      (Primrec.ite (Primrec.eq.comp i B') (Primrec.succ.comp E) (Primrec.nat_add.comp W (Primrec.nat_sub.comp i B')))
  have ixG := Primrec.nat_add.comp (Primrec.nat_add.comp A B') i
  have ixG' : Primrec (fun q : P => placeGraph q.1.2.2.2.1.1 q.1.2.2.2.2.1.1 q.1.2.2.2.2.2.1 q.2) :=
    Primrec.ite (Primrec.nat_lt.comp i C') ixG (Primrec.nat_add.comp ixG (Primrec.const 2))
  have t₁ := Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp (Primrec.succ.comp a) g)) ixB.to₂
  have t₂ := Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp (Primrec.succ.comp b) g)) ixC.to₂
  have t₃ := Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp c (Primrec.const 2))) ixG'.to₂
  have R₁ := renameFormulaProgram.comp (ctx.pair (t₁.pair (Primrec.snd.comp B))).to_comp
  have R₂ := renameFormulaProgram.comp (ctx.pair (t₂.pair (Primrec.snd.comp C))).to_comp
  have R₃ := renameFormulaProgram.comp (ctx.pair (t₃.pair (Primrec.snd.comp G))).to_comp
  have n' := litProgram.comp (Primrec.nat_add.comp (Primrec.nat_add.comp n lv) (Primrec.const 2))
  have step := eqProgram.comp (varProgram.comp (Primrec.nat_add.comp e (Primrec.const 2)))
    (addProgram.comp (addProgram.comp n' (varProgram.comp e)) (varProgram.comp (Primrec.succ.comp e)))
  exact w.to_comp.pair (andProgram.to_comp.comp (andProgram.to_comp.comp R₁ R₂)
    (andProgram.to_comp.comp step.to_comp R₃))

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
