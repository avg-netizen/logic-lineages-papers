module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateVertexPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

theorem add_raw_primitive :
    Primrec (fun p : List Nat × Nat × Nat × Nat × Nat => addRaw p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let A := List Nat × Nat × Nat × Nat × Nat
  have hctx : Primrec (fun p : A => p.1) := Primrec.fst
  have ha : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : A => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec (fun p : A => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have erase (x y : A → Nat) (hx : Primrec x) (hy : Primrec y) :
      Primrec (fun p => eraseRaw p.1 (x p) (y p)) :=
    erase_raw_primitive.comp (hctx.pair (hx.pair hy))
  have he₁ := (erase _ _ hb (Primrec.const 0)).pair (erase _ _ (Primrec.const 0) hd)
  have he₂ := (erase _ _ ha hd).pair (erase _ _ hc (Primrec.const 0))
  exact Primrec.list_cons.comp he₁
    (Primrec.list_cons.comp he₂ (Primrec.const ([] : List (Code × Code))))

theorem unused_raw_primitive : Primrec (fun p : List Nat × Nat => unusedRaw p.1 p.2) := by
  let A := List Nat × Nat
  have hctx : Primrec (fun p : A × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : A × Nat => p.2 + 1) :=
    Primrec.nat_add.comp Primrec.snd (Primrec.const 1)
  have hrow := (port_raw_primitive.comp (hctx.pair hi)).pair
    (port_raw_primitive.comp (hctx.pair (Primrec.const 0)))
  exact Primrec.list_map
    (Primrec.list_drop.comp (Primrec.snd : Primrec (fun p : A => p.2)) (Primrec.const (List.range 9)))
    hrow.to₂

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
