module
public import LogicLineages.OrdinalComparison.NumericUnaryChainTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem shift_primitive : Primrec (fun p : Nat×Nat×RawPair => shiftPair p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat×Nat×RawPair => p.1) := Primrec.fst
  have hc : Primrec (fun p : Nat×Nat×RawPair => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Nat×Nat×RawPair => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hv : Primrec (fun p : Nat×Nat×RawPair => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp (hd.pair (hc.pair hs))).pair
    (ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.2.2.comp (hd.pair (hc.pair hv)))

private theorem context_primitive : Primrec₂ contextCode := by
  have hs : Primrec (fun p : (List Nat×List RawOperator)×RawOperator×List Nat => p.2.1.1++p.2.2) :=
    Primrec.list_append.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd Primrec.fst hs.to₂

private def mergeStep (p : RawOperator×(Nat×List RawPair)) : Nat×List RawPair :=
  (p.1.1.length+p.2.1,shiftPair p.1.1.length p.2.1 (p.1.2.1,p.1.2.2) :: p.2.2.map (shiftPair 0 p.1.1.length))

private theorem merge_step_primitive : Primrec mergeStep := by
  have hd : Primrec (fun p : RawOperator×(Nat×List RawPair) => p.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun p : RawOperator×(Nat×List RawPair) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun p : RawOperator×(Nat×List RawPair) => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun p : RawOperator×(Nat×List RawPair) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hhead := shift_primitive.comp (hd.pair (hn.pair hp))
  have htail := Primrec.list_map ht
    (shift_primitive.comp ((Primrec.const 0).pair ((hd.comp Primrec.fst).pair Primrec.snd))).to₂
  exact (Primrec.nat_add.comp hd hn).pair (Primrec.list_cons.comp hhead htail)

private theorem merge_primitive : Primrec mergeData := by
  have h := Primrec.list_foldr (Primrec.id (α := List RawOperator)) (Primrec.const ((0,[]) : Nat×List RawPair))
    (merge_step_primitive.comp Primrec.snd).to₂
  apply h.of_eq
  intro ops
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    simp only [id_eq,List.foldr_cons,mergeData]
    simp only [id_eq] at ih
    rw [ih]
    rfl

private theorem body_primitive : Primrec bodyCode := by
  have hs : Primrec (fun p : List Nat×Nat×Nat =>
      8*Nat.pair (ContextInsertionCode.sourceCode 0 1 p.2.1) p.2.2+5) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp
        (ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
          ((Primrec.const 0).pair ((Primrec.const 1).pair (Primrec.fst.comp Primrec.snd))))
        (Primrec.snd.comp Primrec.snd))) (Primrec.const 5)
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hs.to₂

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  have hc : Primrec chainCode := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp (Primrec.const 0) body_primitive)) (Primrec.const 6)
  refine ⟨context_primitive,merge_primitive,hc,?_⟩
  have hctx : Primrec (fun p : List Nat×List RawOperator => contextCode p.1 p.2) := context_primitive
  have hterms : Primrec (fun p : List Nat×List RawOperator => (mergeData p.2).2.map Prod.fst) :=
    Primrec.list_map (Primrec.snd.comp (merge_primitive.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd).to₂
  have hsrc := hc.comp hterms
  have ha := DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp (hctx.pair hsrc)
  have hout : Primrec (fun q : (List Nat×List RawOperator)×List Nat =>
      (contextCode q.1.1 q.1.2,chainCode ((mergeData q.1.2).2.map Prod.fst),q.2)) :=
    (hctx.comp Primrec.fst).pair ((hsrc.comp Primrec.fst).pair Primrec.snd)
  have h := Primrec.option_map ha hout.to₂
  apply h.of_eq
  intro p
  cases hassign : DefaultSourceAssignment.assignmentCode (contextCode p.1 p.2) (chainCode ((mergeData p.2).2.map Prod.fst)) <;> simp [compileCode,hassign]
end LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Proof
