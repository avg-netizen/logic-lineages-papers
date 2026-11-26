module
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanRenamingPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler

open PlanCompiler (Instruction)

theorem gate_primitive : Primrec gate :=
  Primrec.sumInr.comp Primrec.sumInl

theorem shift_port_primitive : Primrec (fun p : Nat × Nat => shiftPort p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.snd Primrec.fst)

theorem prefix_table_primitive :
    Primrec (fun p : Nat × List Nat => prefixTable p.1 p.2) := by
  let A := Nat × List Nat
  have hn : Primrec (fun p : A × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
    (Primrec.nat_add.comp Primrec.snd hn).to₂

theorem binary_step_primitive :
    Primrec (fun p : BinaryState × Nat => binaryStep p.1 p.2) := by
  let A := BinaryState × Nat
  have hstate : Primrec (fun p : A => p.1) := Primrec.fst
  have hctx := Primrec.fst.comp hstate
  have hout := Primrec.fst.comp (Primrec.snd.comp hstate)
  have htail := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hstate))
  have hpending := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hstate))
  have target (n : Nat) : Primrec (fun p : A => List.replicate n 0 ++ p.1.1) :=
    Primrec.list_append.comp (Primrec.const (List.replicate n 0)) hctx
  have renamed (n : Nat) : Primrec (fun p : A =>
      PlanRenaming.renamePlanRaw (List.replicate n 0 ++ p.1.1)
        (prefixTable n p.1.1) p.1.2.2.1) :=
    PlanRenaming.primitive.comp ((target n).pair
      ((prefix_table_primitive.comp ((Primrec.const n).pair hctx)).pair htail))
  have add (n a b : Nat) : Primrec (fun p : A => gate (1,a,b,shiftPort n p.1.2.1,0)) :=
    gate_primitive.comp ((Primrec.const 1).pair ((Primrec.const a).pair ((Primrec.const b).pair
      ((shift_port_primitive.comp ((Primrec.const n).pair hout)).pair (Primrec.const 0)))))
  have hend (n : Nat) : Primrec (fun p : A => p.1.2.2.2 + n) :=
    Primrec.nat_add.comp hpending (Primrec.const n)
  have hdouble := (target 1).pair ((Primrec.const 1).pair
    ((Primrec.list_cons.comp (add 1 1 1) (renamed 1)).pair (hend 1)))
  have hthree := Primrec.list_cons.comp (Primrec.const (gate (1,3,3,2,0)))
    (Primrec.list_cons.comp (Primrec.const (gate (3,1,0,0,0)))
      (Primrec.list_cons.comp (add 3 2 1) (renamed 3)))
  have hdoubleOne := (target 3).pair ((Primrec.const 3).pair (hthree.pair (hend 3)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) hdouble hdoubleOne

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler
