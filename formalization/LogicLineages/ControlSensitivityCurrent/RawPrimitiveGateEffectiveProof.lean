module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateForestPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

theorem gate_guard_primitive : Primrec (fun p : List Nat × GateCode => gateGuard p.1 p.2) := by
  let A := List Nat × GateCode
  have hctx : Primrec (fun p : A => p.1) := Primrec.fst
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hc : Primrec (fun p : A => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hd : Primrec (fun p : A => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hports := Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp (port_guard_primitive.comp (hctx.pair ha))
      (port_guard_primitive.comp (hctx.pair hb)))
    (port_guard_primitive.comp (hctx.pair hc)))
    (port_guard_primitive.comp (hctx.pair hd))
  have ht (n : Nat) : PrimrecPred (fun p : A => p.2.1 = n) := Primrec.eq.comp htag (Primrec.const n)
  have hb0 := Primrec.eq.comp hb (Primrec.const 0)
  have hc0 := Primrec.eq.comp hc (Primrec.const 0)
  have hd0 := Primrec.eq.comp hd (Primrec.const 0)
  have heq := ((ht 0).and (hc0.and hd0)).decide
  have hadd := ((ht 1).and hd0).decide
  have hsort := (ht 2).decide
  have hone := ((ht 3).and (hb0.and (hc0.and hd0))).decide
  exact Primrec.and.comp hports (Primrec.or.comp
    (Primrec.or.comp (Primrec.or.comp heq hadd) hsort) hone)

theorem effective : RawPrimitiveGateTargets.Effective := by
  apply (Computable.cond gate_guard_primitive.to_comp
    (Computable.option_some.comp forest_raw_primitive.to_comp) (Computable.const none)).of_eq
  intro p
  cases h : gateGuard p.1 p.2 <;> simp [compile, h]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
