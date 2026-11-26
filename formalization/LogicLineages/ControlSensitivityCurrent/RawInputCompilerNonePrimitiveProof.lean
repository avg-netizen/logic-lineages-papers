module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerStatePrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open PlanCompiler (Instruction)
open BooleanMatrix (RowCode)
open PrimitiveGate (port_guard_primitive)
open BinaryPlanCompiler (binder gate_primitive shift_port_primitive)

theorem advance_none_primitive :
    Primrec (fun p : InputState × RowCode => advance p.1 (p.2,none)) := by
  let A := InputState × RowCode
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hr : Primrec (fun p : A => p.2) := Primrec.snd
  have hctx := Primrec.fst.comp hs
  have hm := Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp hs))
  have htag := Primrec.fst.comp hr
  have ha := Primrec.fst.comp (Primrec.snd.comp hr)
  have hb := Primrec.snd.comp (Primrec.snd.comp hr)
  have hbool := boolean_guard_primitive.comp (hctx.pair (hm.pair hr))
  have hportA := port_guard_primitive.comp (hctx.pair ha)
  have hportB := port_guard_primitive.comp (hctx.pair hb)
  have hboth := (Primrec.eq.comp hportA (Primrec.const true)).and
    (Primrec.eq.comp hportB (Primrec.const true))
  have htagIs (n : Nat) : PrimrecPred (fun p : A => p.2.1 = n) :=
    Primrec.eq.comp htag (Primrec.const n)
  have hboolStep := Primrec.ite (Primrec.eq.comp hbool (Primrec.const true))
    (Primrec.option_some.comp add_row_primitive) (Primrec.const none)
  have lift (f : A → Nat) (hf : Primrec f) : Primrec (fun p => BinaryPlanCompiler.shiftPort 1 (f p)) :=
    shift_port_primitive.comp ((Primrec.const 1).pair hf)
  have hgate := gate_primitive.comp ((Primrec.const 1).pair
    ((lift _ ha).pair ((lift _ hb).pair (Primrec.const (1,0)))))
  have hchunk := Primrec.list_cons.comp (Primrec.const binder)
    (Primrec.list_cons.comp hgate (Primrec.const ([] : List Instruction)))
  have hadd := Primrec.option_some.comp (add_wire_primitive.comp (hs.pair
    (hchunk.pair (Primrec.const (([],none) : List Nat × Option Nat)))))
  have hliteral := Primrec.option_some.comp (add_wire_primitive.comp (hs.pair
    ((Primrec.const ([] : List Instruction)).pair (hctx.pair (Primrec.option_some.comp ha)))))
  exact Primrec.ite (Primrec.nat_lt.comp htag (Primrec.const 6)) hboolStep
    (Primrec.ite ((htagIs 6).and hboth) hadd
      (Primrec.ite ((htagIs 7).and (Primrec.eq.comp hb (Primrec.const 0))) hliteral (Primrec.const none)))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
