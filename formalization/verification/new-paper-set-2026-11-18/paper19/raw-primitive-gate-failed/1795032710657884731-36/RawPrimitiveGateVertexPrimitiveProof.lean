module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

open LogicLineages.OrdinalComparison.Source
open CheckedComposition (rawNode)

theorem block_context_primitive : Primrec blockContext :=
  Primrec.list_append.comp (Primrec.const (List.replicate 9 0)) Primrec.id

theorem lift_port_primitive : Primrec liftPortRaw :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.id (Primrec.const 9))

theorem port_guard_primitive : Primrec (fun p : List Nat × Nat => portGuard p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const true)
    (RawValidator.variable_primitive.comp (Primrec.fst.pair ((Primrec.const 0).pair
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))))

theorem port_node_primitive : Primrec (fun p : List Nat × Nat => portNode p.1 p.2) := by
  have hindex : Primrec (fun p : List Nat × Nat => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hargs := Primrec.list_cons.comp hindex (Primrec.const ([] : List Nat))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.fst.pair (Primrec.const ((0,3,[]) : Nat × Nat × List Nat)))
    (Primrec.fst.pair ((Primrec.const 0).pair ((Primrec.const 0).pair hargs)))

theorem port_raw_primitive : Primrec (fun p : List Nat × Nat => portRaw p.1 p.2) := by
  have hnode := port_node_primitive.comp ((Primrec.const ([] : List Nat)).pair Primrec.snd)
  exact Primrec.fst.pair
    ((Primrec.list_cons.comp hnode (Primrec.const ([] : List Node))).pair (Primrec.const (0,0)))

theorem successor_raw_primitive : Primrec (fun p : List Nat × Nat => successorRaw p.1 p.2) := by
  have hnode := port_node_primitive.comp ((Primrec.const ([] : List Nat)).pair Primrec.snd)
  have htail := Primrec.list_cons.comp hnode (Primrec.const ([] : List Node))
  have htable := Primrec.list_cons.comp (Primrec.const (rawNode 0 1 [0,0,1]))
    (Primrec.list_cons.comp (Primrec.const (rawNode (SyntaxCode.arrowCode 0 0) 4 [])) htail)
  exact Primrec.fst.pair (htable.pair (Primrec.const (0,0)))

theorem erase_raw_primitive : Primrec (fun p : List Nat × Nat × Nat => eraseRaw p.1 p.2.1 p.2.2) := by
  let A := List Nat × Nat × Nat
  have ha : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hin := Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp ha (Primrec.const 1))
  have hbody := port_node_primitive.comp ((Primrec.const ([0] : List Nat)).pair hin)
  have harg := port_node_primitive.comp ((Primrec.const ([] : List Nat)).pair hb)
  have htail := Primrec.list_cons.comp hbody (Primrec.const ([] : List Node))
  have htable := Primrec.list_cons.comp (Primrec.const (rawNode 0 1 [0,1,0]))
    (Primrec.list_cons.comp harg (Primrec.list_cons.comp
      (Primrec.const (rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,0])) htail))
  exact Primrec.fst.pair (htable.pair (Primrec.const (0,0)))

theorem identity_zero_raw_primitive : Primrec identityZeroRaw :=
  Primrec.id.pair (Primrec.const
    ([rawNode 0 1 [0,1,0], portNode [] 0, rawNode (SyntaxCode.arrowCode 0 0) 2 [0,0,0],
      portNode [0] 1],0,0))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
