module
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode.Proof

theorem eraser_primitive : Primrec₂ eraserCode := by
  have hs : Primrec (fun p : Nat×Nat => ContextInsertionCode.sourceCode 0 1 p.1) :=
    ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
      ((Primrec.const 0).pair ((Primrec.const 1).pair Primrec.fst))
  have hl : Primrec (fun p : Nat×Nat => 8*Nat.pair 0 (ContextInsertionCode.sourceCode 0 1 p.1)+6) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.const 0) hs)) (Primrec.const 6)
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp hl Primrec.snd)) (Primrec.const 5)

theorem left_primitive : Primrec₂ leftCode :=
  eraser_primitive.comp (eraser_primitive.comp Primrec.fst Primrec.fst)
    (eraser_primitive.comp Primrec.snd Primrec.snd)
theorem right_primitive : Primrec₂ rightCode :=
  eraser_primitive.comp (eraser_primitive.comp Primrec.fst Primrec.snd)
    (eraser_primitive.comp Primrec.snd Primrec.fst)
theorem step_primitive : Primrec₂ step := by
  have ha : Primrec (fun p : (Nat×Nat)×(Nat×Nat) =>
      eraserCode (leftCode p.1.1 p.1.2) p.2.1) :=
    eraser_primitive.comp (left_primitive.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : (Nat×Nat)×(Nat×Nat) =>
      eraserCode (rightCode p.1.1 p.1.2) p.2.2) :=
    eraser_primitive.comp (right_primitive.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd)
  exact ha.pair hb

theorem aggregate_primitive : Primrec aggregateCode := by
  have hs : Primrec (fun p : List (Nat×Nat) × (Nat×Nat) × (Nat×Nat) => step p.2.1 p.2.2) :=
    step_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const ((1,1) : Nat×Nat)) hs.to₂

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨eraser_primitive,left_primitive,right_primitive,step_primitive,aggregate_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregateCode.Proof
