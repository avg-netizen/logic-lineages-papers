module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateGadgetPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

theorem forest_raw_primitive : Primrec (fun p : List Nat × GateCode => forestRaw p.1 p.2) := by
  let A := List Nat × GateCode
  have hctx : Primrec (fun p : A => blockContext p.1) := block_context_primitive.comp Primrec.fst
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : A => liftPortRaw p.2.2.1) :=
    lift_port_primitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun p : A => liftPortRaw p.2.2.2.1) :=
    lift_port_primitive.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : Primrec (fun p : A => liftPortRaw p.2.2.2.2.1) :=
    lift_port_primitive.comp (Primrec.fst.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hd : Primrec (fun p : A => liftPortRaw p.2.2.2.2.2) :=
    lift_port_primitive.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have port (v : A → Nat) (hv : Primrec v) : Primrec (fun p => portRaw (blockContext p.1) (v p)) :=
    port_raw_primitive.comp (hctx.pair hv)
  have successor (v : A → Nat) (hv : Primrec v) :
      Primrec (fun p => successorRaw (blockContext p.1) (v p)) :=
    successor_raw_primitive.comp (hctx.pair hv)
  have add (a b c d : A → Nat) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hd : Primrec d) :
      Primrec (fun p => addRaw (blockContext p.1) (a p) (b p) (c p) (d p)) :=
    add_raw_primitive.comp (hctx.pair (ha.pair (hb.pair (hc.pair hd))))
  have unused (start : Nat) : Primrec (fun p : A => unusedRaw (blockContext p.1) start) :=
    unused_raw_primitive.comp (hctx.pair (Primrec.const start))
  have heq := Primrec.list_cons.comp ((port _ ha).pair (port _ hb)) (unused 0)
  have hadd := Primrec.list_append.comp (add _ _ _ _ ha hb hc (Primrec.const 1)) (unused 1)
  have hs₁ := (successor _ ha).pair (port _ (Primrec.const 1))
  have hs₂ := (successor _ hb).pair (port _ (Primrec.const 2))
  have hs₃ := (successor _ hc).pair (port _ (Primrec.const 3))
  have hs₄ := (successor _ hd).pair (port _ (Primrec.const 4))
  have hsortHead := Primrec.list_cons.comp hs₁ (Primrec.list_cons.comp hs₂
    (Primrec.list_cons.comp hs₃ (Primrec.list_cons.comp hs₄ (Primrec.const []))))
  have hsortTail₁ := add _ _ _ _ (Primrec.const 1) (Primrec.const 2) (Primrec.const 5) (Primrec.const 7)
  have hsortTail₂ := add _ _ _ _ (Primrec.const 3) (Primrec.const 4) (Primrec.const 5) (Primrec.const 8)
  have hsortTail₃ := add _ _ _ _ hc (Primrec.const 6) hd (Primrec.const 9)
  have hsort := Primrec.list_append.comp hsortHead
    (Primrec.list_append.comp hsortTail₁ (Primrec.list_append.comp hsortTail₂ hsortTail₃))
  have honeHead := (successor _ (Primrec.const 1)).pair (identity_zero_raw_primitive.comp hctx)
  have honeTail := Primrec.list_append.comp (add _ _ _ _ ha ha (Primrec.const 1) (Primrec.const 2)) (unused 2)
  have hone := Primrec.list_cons.comp honeHead honeTail
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) heq
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hadd
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hsort hone))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
