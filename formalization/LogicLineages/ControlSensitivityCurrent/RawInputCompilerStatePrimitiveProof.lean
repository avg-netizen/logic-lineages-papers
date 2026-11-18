module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanStepPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open PrimitiveGate (port_guard_primitive)
open BooleanMatrix (RowCode)
open BinaryPlanCompiler (shift_port_primitive)

theorem boolean_guard_primitive :
    Primrec (fun p : List Nat × Nat × RowCode => booleanGuard p.1 p.2.1 p.2.2) := by
  let A := List Nat × Nat × RowCode
  have hctx : Primrec (fun p : A => p.1) := Primrec.fst
  have hm : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have htag := Primrec.fst.comp hr
  have ha := Primrec.fst.comp (Primrec.snd.comp hr)
  have hb := Primrec.snd.comp (Primrec.snd.comp hr)
  have hport := Primrec.and.comp (port_guard_primitive.comp (hctx.pair ha))
    (port_guard_primitive.comp (hctx.pair hb))
  have hneg := ((Primrec.nat_lt.comp ha hm).and (Primrec.eq.comp hb (Primrec.const 0))).decide
  have htags := (Primrec.eq.comp htag (Primrec.const 4)).or (Primrec.eq.comp htag (Primrec.const 5))
  have hbinary := (htags.and ((Primrec.nat_lt.comp ha hm).and (Primrec.nat_lt.comp hb hm))).decide
  exact Primrec.ite (Primrec.nat_lt.comp htag (Primrec.const 3)) hport
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hneg hbinary)

theorem add_row_primitive :
    Primrec (fun p : InputState × RowCode => addRow p.1 p.2) := by
  let A := InputState × RowCode
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hr : Primrec (fun p : A => p.2) := Primrec.snd
  have hctx := Primrec.fst.comp hs
  have hrows := Primrec.fst.comp (Primrec.snd.comp hs)
  have hports := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hpending := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have htag := Primrec.fst.comp hr
  have ha := Primrec.fst.comp (Primrec.snd.comp hr)
  have hb := Primrec.snd.comp (Primrec.snd.comp hr)
  have hlength := Primrec.list_length.comp hports
  have hrow := htag.pair (hlength.pair (Primrec.nat_add.comp hlength (Primrec.const 1)))
  have hpair := Primrec.list_cons.comp ha (Primrec.list_cons.comp hb (Primrec.const ([] : List Nat)))
  have hii := hctx.pair ((Primrec.list_cons.comp hrow hrows).pair
    ((Primrec.list_append.comp hports hpair).pair hpending))
  have hll := hctx.pair ((Primrec.list_cons.comp hr hrows).pair
    ((Primrec.list_append.comp hports (Primrec.const ([0,0] : List Nat))).pair hpending))
  exact Primrec.ite (Primrec.nat_lt.comp htag (Primrec.const 3)) hii hll

theorem add_wire_primitive :
    Primrec (fun p : InputState × Lowering => addWire p.1 p.2) := by
  let A := InputState × Lowering
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hctx := Primrec.fst.comp hs
  have hrows := Primrec.fst.comp (Primrec.snd.comp hs)
  have hports := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hpending := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hshift : Primrec (fun xs : List Nat => xs.map (BinaryPlanCompiler.shiftPort 1)) :=
    Primrec.list_map Primrec.id
      (shift_port_primitive.comp ((Primrec.const 1).pair
        (Primrec.snd : Primrec (fun p : List Nat × Nat => p.2)))).to₂
  exact (Primrec.list_cons.comp (Primrec.const 0) hctx).pair (hrows.pair
    ((hshift.comp hports).pair (Primrec.list_cons.comp Primrec.snd hpending)))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
