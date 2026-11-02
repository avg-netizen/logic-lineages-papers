module
public import LogicLineages.OrdinalComparison.NumericCarrierDataTargets
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodePrimitiveProof
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeProof
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericCarrierData.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem fresh_primitive : Primrec freshOrdinal := by
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 8))
  have hi := Primrec.fst.comp hp
  have hj := Primrec.snd.comp hp
  have hn := Primrec.ite (Primrec.eq.comp hi (Primrec.const 0)) (Primrec.const 0) (Primrec.succ.comp hi)
  have hl : Primrec freshLeaf := Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 8)) (Primrec.const 3))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp hn hj))
      (Primrec.const 3)) Primrec.id
  have hb : Primrec (fun p : Nat×Nat×Nat => 8*Nat.pair p.2.1 p.2.2+p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))) Primrec.fst
  exact OrdinalSyntax.ordinalSyntaxFoldPrimitiveRecursive _ _ _ hl hb

private theorem fresh_vector_primitive : Primrec freshVector :=
  Primrec.list_map Primrec.id (fresh_primitive.comp Primrec.snd).to₂

private theorem sat_source_step (r n : Nat) :
    saturateSource (r+1) n = 8*Nat.pair (saturateSource r n) 1+5 := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => exact ih _

private theorem sat_vector_step (r : Nat) (v : List Nat) :
    saturateVector (r+1) v = OrdinalSyntax.defaultApplicationCode 1 0 (saturateVector r v) [1] := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih => exact ih _

private theorem sat_source_primitive : Primrec₂ saturateSource := by
  have hs : Primrec (fun p : Nat×Nat×Nat => 8*Nat.pair p.2.2 1+5) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1))) (Primrec.const 5)
  have h := Primrec.nat_rec Primrec.id hs.to₂
  have hh : Primrec₂ (fun n r : Nat => saturateSource r n) := by
    apply h.of_eq
    intro n r
    induction r with
    | zero => rfl
    | succ r ih => change 8*Nat.pair (Nat.rec _ _ r) 1+5 = _;rw [ih,sat_source_step]
  exact hh.comp Primrec.snd Primrec.fst

private theorem app_primitive : Primrec (fun v : List Nat => OrdinalSyntax.defaultApplicationCode 1 0 v [1]) :=
  OrdinalSyntax.defaultSyntaxApplicationPrimitiveRecursive.comp
    ((Primrec.const 1).pair ((Primrec.const 0).pair (Primrec.id.pair (Primrec.const [1]))))

private theorem sat_vector_primitive : Primrec₂ saturateVector := by
  have hs : Primrec (fun p : List Nat×Nat×List Nat => OrdinalSyntax.defaultApplicationCode 1 0 p.2.2 [1]) :=
    app_primitive.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec Primrec.id hs.to₂
  have hh : Primrec₂ (fun v : List Nat => fun r : Nat => saturateVector r v) := by
    apply h.of_eq
    intro v r
    induction r with
    | zero => rfl
    | succ r ih => change OrdinalSyntax.defaultApplicationCode 1 0 (Nat.rec _ _ r) [1] = _;rw [ih,sat_vector_step]
  exact hh.comp Primrec.snd Primrec.fst

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  refine ⟨fresh_primitive,fresh_vector_primitive,sat_source_primitive,sat_vector_primitive,?_⟩
  have hctx : Primrec (fun p : List Nat×Nat => p.1.getD 0 0 :: p.1) :=
    Primrec.list_cons.comp ((Primrec.list_getD (0 : Nat)).comp Primrec.fst (Primrec.const 0)) Primrec.fst
  have hr : Primrec (fun p : List Nat×Nat => SourceAnnotationCode.operatorArity p.2) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hp : Primrec (fun p : List Nat×Nat => p.2.unpair.2.unpair) := Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hs : Primrec (fun p : List Nat×Nat => SourceAnnotationCode.operatorSource p.2) := Primrec.fst.comp hp
  have hv : Primrec (fun p : List Nat×Nat => SourceAnnotationCode.operatorVector p.2) :=
    Primrec.option_getD.comp (Primrec.decode.comp (Primrec.snd.comp hp)) (Primrec.const [])
  have hsrc := GroundCaptureClosingCode.Proof.primitiveRecursiveAlgorithms.1.comp
    (hctx.pair ((Primrec.const 0).pair (sat_source_primitive.comp hr
      (SourceCarrierMapCode.Proof.primitiveRecursive.comp ((Primrec.const true).pair ((Primrec.const 0).pair hs))))))
  have hvec := GroundCaptureClosingCode.Proof.primitiveRecursiveAlgorithms.2.2.comp hctx
    (sat_vector_primitive.comp hr (fresh_vector_primitive.comp hv))
  exact Primrec₂.natPair.comp (Primrec.const 0) (Primrec₂.natPair.comp hsrc (Primrec.encode.comp hvec))
end LogicLineages.OrdinalComparison.Source.NumericCarrierData.Proof
