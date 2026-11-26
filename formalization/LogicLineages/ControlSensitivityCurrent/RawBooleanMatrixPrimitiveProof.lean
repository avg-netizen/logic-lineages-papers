module
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixLocalPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix

open PrimitiveGate (GateCode)
open BinaryPlanCompiler (gate gate_primitive binders_primitive)

theorem emit_row_primitive :
    Primrec (fun p : Nat × List Nat × RowState × RowCode => emitRow p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × List Nat × RowState × RowCode
  have hm : Primrec (fun p : A => p.1) := Primrec.fst
  have hports : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hstate : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrow : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hi := Primrec.nat_sub.comp (Primrec.fst.comp hstate) (Primrec.const 1)
  have hnew := local_raw_primitive.comp (hm.pair (hports.pair (hi.pair hrow)))
  exact hi.pair (Primrec.list_append.comp (Primrec.snd.comp hstate) hnew)

theorem emit_rows_primitive :
    Primrec (fun p : Nat × List Nat × Nat × List RowCode => emitRows p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × List Nat × Nat × List RowCode
  let B := A × (RowState × RowCode)
  have hm : Primrec (fun p : A => p.1) := Primrec.fst
  have hports : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrows : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hstep := emit_row_primitive.comp ((hm.comp Primrec.fst).pair ((hports.comp Primrec.fst).pair
    (Primrec.snd : Primrec (fun p : B => p.2))))
  exact Primrec.list_foldl (Primrec.list_reverse.comp hrows)
    ((Primrec.nat_add.comp hi (Primrec.list_length.comp hrows)).pair
      (Primrec.const ([] : List GateCode))) hstep.to₂

theorem primitive : RawBooleanMatrixTargets.Primitive := by
  let A := List Nat × List RowCode × Nat
  have hports : Primrec (fun p : A => p.1) := Primrec.fst
  have hrows : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hroot : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hm := Primrec.list_length.comp hrows
  have hrowsOut := Primrec.snd.comp (emit_rows_primitive.comp
    (hm.pair (hports.pair ((Primrec.const 0).pair hrows))))
  have hone := one_code_primitive.comp hm
  have start : Primrec (fun p : A => ((3,oneCode p.2.1.length,0,0,0) : GateCode)) :=
    (Primrec.const 3).pair (hone.pair (Primrec.const (0,0,0)))
  have final : Primrec (fun p : A => eqCode (bitCode p.2.2) (oneCode p.2.1.length)) :=
    (Primrec.const 0).pair ((bit_code_primitive.comp hroot).pair (hone.pair (Primrec.const (0,0))))
  have htail := Primrec.list_cons.comp final (Primrec.const ([] : List GateCode))
  have hgates := Primrec.list_cons.comp start (Primrec.list_append.comp hrowsOut htail)
  have hmap := Primrec.list_map hgates (gate_primitive.comp
    (Primrec.snd : Primrec (fun p : A × GateCode => p.2))).to₂
  exact Primrec.list_append.comp (binders_primitive.comp hone) hmap

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix
