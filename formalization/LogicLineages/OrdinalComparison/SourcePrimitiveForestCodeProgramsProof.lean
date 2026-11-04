module
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeTargets
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Proof

theorem shift_primitive : Primrec₂ shiftPort :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.snd Primrec.fst)
theorem port_primitive : Primrec portCode :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 8) (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
theorem successor_primitive : Primrec successorCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp (Primrec.const 2) port_primitive)) (Primrec.const 5)
theorem eraser_primitive : Primrec₂ eraserCode :=
  SourceGammaAggregateCode.Proof.eraser_primitive.comp
    (port_primitive.comp Primrec.fst) (port_primitive.comp Primrec.snd)

theorem addPairs_primitive : Primrec (fun p : Nat×Nat×Nat×Nat => addPairs p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ha : Primrec (fun p : Nat×Nat×Nat×Nat => p.1) := Primrec.fst
  have hb : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h1 := (eraser_primitive.comp hb (Primrec.const 0)).pair (eraser_primitive.comp (Primrec.const 0) hd)
  have h2 := (eraser_primitive.comp ha hd).pair (eraser_primitive.comp hc (Primrec.const 0))
  exact Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.const []))

theorem unused_primitive : Primrec unusedPairs := by
  have hp : PrimrecRel (fun i start : Nat => start ≤ i) := Primrec.nat_le.comp Primrec.snd Primrec.fst
  have hf : Primrec (fun start : Nat => (List.range 9).filter (fun i => start ≤ i)) :=
    (PrimrecRel.listFilter hp).comp (Primrec.const (List.range 9)) Primrec.id
  have he : Primrec (fun p : Nat×Nat => (portCode (p.2+1),1)) :=
    (port_primitive.comp (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))).pair (Primrec.const 1)
  exact Primrec.list_map hf he.to₂

attribute [local irreducible] shiftPort portCode successorCode eraserCode addPairs unusedPairs

theorem eq_primitive : Primrec₂ eqForest := by
  have ha := port_primitive.comp (shift_primitive.comp (Primrec.const 9) (Primrec.fst (α:=Nat) (β:=Nat)))
  have hb := port_primitive.comp (shift_primitive.comp (Primrec.const 9) (Primrec.snd (α:=Nat) (β:=Nat)))
  exact Primrec.list_cons.comp (ha.pair hb) (Primrec.const (unusedPairs 0))

theorem add_primitive : Primrec (fun p : Nat×Nat×Nat => addForest p.1 p.2.1 p.2.2) := by
  have ha : Primrec (fun p : Nat×Nat×Nat => shiftPort 9 p.1) := shift_primitive.comp (Primrec.const 9) Primrec.fst
  have hb : Primrec (fun p : Nat×Nat×Nat => shiftPort 9 p.2.1) := shift_primitive.comp (Primrec.const 9) (Primrec.fst.comp Primrec.snd)
  have hc : Primrec (fun p : Nat×Nat×Nat => shiftPort 9 p.2.2) := shift_primitive.comp (Primrec.const 9) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_append.comp (addPairs_primitive.comp (ha.pair (hb.pair (hc.pair (Primrec.const 1)))))
    (Primrec.const (unusedPairs 1))

theorem one_primitive : Primrec oneForest := by
  have ha : Primrec (fun a : Nat => shiftPort 9 a) := shift_primitive.comp (Primrec.const 9) Primrec.id
  have ht := Primrec.list_append.comp (addPairs_primitive.comp (ha.pair (ha.pair ((Primrec.const 1).pair (Primrec.const 2)))))
    (Primrec.const (unusedPairs 2))
  exact Primrec.list_cons.comp (Primrec.const (successorCode 1,identityZeroCode)) ht

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨shift_primitive,port_primitive,successor_primitive,eraser_primitive,addPairs_primitive,
    unused_primitive,eq_primitive,add_primitive,one_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourcePrimitiveForestCode.Proof
