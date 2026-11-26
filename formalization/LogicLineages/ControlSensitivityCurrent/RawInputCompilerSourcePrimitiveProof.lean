module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanStepPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open PlanCompiler (Instruction)
open BinaryPlanCompiler (binder prefix_table_primitive)
open PrimitiveGate (port_raw_primitive)

theorem equation_chunk_primitive :
    Primrec (fun p : List Nat × Code => equationChunk p.1 p.2) := by
  let A := List Nat × Code
  have hctx : Primrec (fun p : A => p.1) := Primrec.fst
  have htarget := Primrec.list_cons.comp (Primrec.const 0) hctx
  have htable := prefix_table_primitive.comp ((Primrec.const 1).pair hctx)
  have hlift := Operations.rename_code_primitive.comp (htarget.pair (htable.pair Primrec.snd))
  have hvar := port_raw_primitive.comp (htarget.pair (Primrec.const 1))
  have h := (Primrec.sumInl : Primrec (fun p : Code × Code => (.inl p : Instruction))).comp (hlift.pair hvar)
  exact Primrec.list_cons.comp (Primrec.const binder)
    (Primrec.list_cons.comp h (Primrec.const ([] : List Instruction)))

theorem unary_call_primitive :
    Primrec (fun p : List Nat × Code × Nat => unaryCallRaw p.1 p.2.1 p.2.2) := by
  let A := List Nat × Code × Nat
  have hctx : Primrec (fun p : A => p.1) := Primrec.fst
  have hh : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hf := Operations.rename_code_primitive.comp (hctx.pair ((Primrec.const ([] : List Nat)).pair hh))
  have ha := port_raw_primitive.comp (hctx.pair (Primrec.nat_add.comp hx (Primrec.const 1)))
  exact CheckedComposition.application_raw_primitive.comp ((Primrec.const 0).pair (hf.pair ha))

theorem input_dag_guard_primitive :
    Primrec (fun p : List Nat × Nat × Code => inputDAGGuard p.1 p.2.1 p.2.2) := by
  let A := List Nat × Nat × Code
  have hctx : Primrec (fun p : A => p.1) := Primrec.fst
  have ht : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hdc := Primrec.fst.comp hd
  have hdt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hd))
  have hv := (RawValidator.check_primitive.of_eq RawValidator.check_eq_valid).comp hd
  exact Primrec.and.comp hv (((Primrec.eq.comp hdc hctx).and (Primrec.eq.comp hdt ht)).decide)

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
