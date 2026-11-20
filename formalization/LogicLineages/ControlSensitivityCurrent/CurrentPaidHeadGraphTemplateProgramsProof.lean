module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphTailProgramsProof
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

attribute [local irreducible] tailBody

private def prefixArgs (q : D) : (Nat×Nat)×Nat×List Nat :=
  let w := directWidth q.1 q.2.1
  ((w,w+1),q.2.2.1,q.2.2.2.2.2.1)

private def tailArgs (q : D) : TailPrograms.Input :=
  (q.1,q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.2)

private theorem prefixArgsProgram : Primrec prefixArgs := by
  have a : Primrec (fun q : D => q.1) := Primrec.fst
  have d : Primrec (fun q : D => q.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun q : D => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have base : Primrec (fun q : D => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tail : Primrec (fun q : D => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have small : Primrec (fun q : D => q.2.2.2.2.1) := Primrec.fst.comp tail
  have points : Primrec (fun q : D => q.2.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp tail)
  have ray : Primrec (fun q : D => q.2.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp tail)
  have w := widthProgram.comp a d
  exact (w.pair (Primrec.succ.comp w)).pair (n.pair points)

private theorem tailArgsProgram : Primrec tailArgs := by
  have a : Primrec (fun q : D => q.1) := Primrec.fst
  have d : Primrec (fun q : D => q.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun q : D => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have base : Primrec (fun q : D => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tail : Primrec (fun q : D => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have small : Primrec (fun q : D => q.2.2.2.2.1) := Primrec.fst.comp tail
  have points : Primrec (fun q : D => q.2.2.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp tail)
  have ray : Primrec (fun q : D => q.2.2.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp tail)
  exact a.pair (d.pair (n.pair (base.pair (small.pair ray))))

private theorem directBodyProgram : Primrec (fun q : D => directBody rawLayout q.1 q.2.1 q.2.2.1
    q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  exact (orProgram.comp (prefixProgram.comp prefixArgsProgram)
    (TailPrograms.tailProgram.comp tailArgsProgram)).of_eq (fun q => by rfl)

attribute [local irreducible] directBody rayPlacement

private abbrev DirectIn := Nat×Block×Nat×Nat×Nat×List Nat×List Nat

private def directRay (q : DirectIn) : Nat :=
  let w := directWidth q.2.1.1 q.2.2.1
  let table := (List.range (q.2.1.1+2+q.1)).map (rayPlacement q.2.1.1)
  MatrixCode.renameFormula (UnitCode.bitCtx (w+2)) table q.2.1.2

private theorem directRayProgram : Computable directRay := by
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
  unfold directRay
  exact rr

private def directArgs (q : DirectIn) : D :=
  (q.2.1.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2.1,q.2.2.2.2.2.2,directRay q)

private theorem directArgsProgram : Computable directArgs := by
  let P := DirectIn
  have g : Primrec (fun q : P => q.1) := Primrec.fst
  have r : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have d : Primrec (fun q : P => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have n : Primrec (fun q : P => q.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have p : Primrec (fun q : P => q.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have wr := Primrec.fst.comp r
  unfold directArgs
  exact wr.to_comp.pair (d.to_comp.pair (n.to_comp.pair
    ((Primrec.fst.comp p).to_comp.pair ((Primrec.fst.comp (Primrec.snd.comp p)).to_comp.pair
      ((Primrec.snd.comp (Primrec.snd.comp p)).to_comp.pair directRayProgram)))))

theorem directBlockProgram : Computable (fun q : Nat×Block×Nat×Nat×Nat×List Nat×List Nat => directBlock q.1 q.2.1 q.2.2.1 q.2.2.2.1
    q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  have d : Primrec (fun q : DirectIn => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have wr : Primrec (fun q : DirectIn => q.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  exact ((widthProgram.comp wr d).to_comp.pair (directBodyProgram.to_comp.comp directArgsProgram)).of_eq
    (fun q => by rfl)
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
