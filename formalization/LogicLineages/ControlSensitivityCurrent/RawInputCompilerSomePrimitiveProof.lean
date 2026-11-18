module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerStatePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerSourcePrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler

open LogicLineages.OrdinalComparison.Source
open BooleanMatrix (RowCode)

theorem advance_some_primitive :
    Primrec (fun p : InputState × RowCode × Code => advance p.1 (p.2.1,some p.2.2)) := by
  let A := InputState × RowCode × Code
  have hs : Primrec (fun p : A => p.1) := Primrec.fst
  have hrow : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hctx := Primrec.fst.comp hs
  have htag := Primrec.fst.comp hrow
  have ha := Primrec.fst.comp (Primrec.snd.comp hrow)
  have hb := Primrec.snd.comp (Primrec.snd.comp hrow)
  have hobs := input_dag_guard_primitive.comp (hctx.pair ((Primrec.const 0).pair hd))
  have hunary := input_dag_guard_primitive.comp ((Primrec.const ([] : List Nat)).pair
    ((Primrec.const (SyntaxCode.arrowCode 0 0)).pair hd))
  have hv := RawValidator.variable_primitive.comp (hctx.pair ((Primrec.const 0).pair ha))
  have hcase (n : Nat) : PrimrecPred (fun p : A => p.2.1.1 = n) :=
    Primrec.eq.comp htag (Primrec.const n)
  have ha0 := Primrec.eq.comp ha (Primrec.const 0)
  have hb0 := Primrec.eq.comp hb (Primrec.const 0)
  have hobsGuard := (hcase 8).and (ha0.and (hb0.and (Primrec.eq.comp hobs (Primrec.const true))))
  have hunaryGuard := (hcase 9).and (hb0.and
    ((Primrec.eq.comp hunary (Primrec.const true)).and (Primrec.eq.comp hv (Primrec.const true))))
  have hcall := unary_call_primitive.comp (hctx.pair (hd.pair ha))
  have emit (f : A → Code) (hf : Primrec f) :
      Primrec (fun p => some (addWire p.1 (equationChunk p.1.1 (f p),[],none))) :=
    Primrec.option_some.comp (add_wire_primitive.comp (hs.pair
      ((equation_chunk_primitive.comp (hctx.pair hf)).pair
        (Primrec.const (([],none) : List Nat × Option Nat)))))
  exact Primrec.ite hobsGuard (emit _ hd) (Primrec.ite hunaryGuard (emit _ hcall) (Primrec.const none))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.InputCompiler
