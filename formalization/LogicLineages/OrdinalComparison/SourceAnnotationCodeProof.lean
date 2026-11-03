module
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeSemanticProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Proof

private theorem node_primitive (radix tag : Nat) : Primrec (fun p : Nat×Nat => radix*Nat.pair p.1 p.2+tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const radix) Primrec₂.natPair) (Primrec.const tag)

private theorem vector_primitive : Primrec operatorVector :=
  Primrec.option_getD.comp (Primrec.decode.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))) (Primrec.const [])

private theorem operator_close_primitive : Primrec closeOperatorCode := by
  have harity : Primrec operatorArity := Primrec.fst.comp Primrec.unpair
  have hsource : Primrec operatorSource := Primrec.fst.comp
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hs := SourceCarrierMapCode.Proof.primitiveRecursive.comp
    ((Primrec.const false).pair ((Primrec.const 0).pair hsource))
  have hv : Primrec (fun n => (operatorVector n).map OrdinalSyntax.headClosure) :=
    Primrec.list_map vector_primitive
      (OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp Primrec.snd).to₂
  exact Primrec₂.natPair.comp harity (Primrec₂.natPair.comp hs (Primrec.encode.comp hv))

private theorem repeat_primitive : Primrec₂ repeatCode := by
  have hbody : Primrec (fun p : Nat × (Nat×Nat) => 4*Nat.pair p.2.2 p.1+2) :=
    (node_primitive 4 2).comp ((Primrec.snd.comp Primrec.snd).pair Primrec.fst)
  have hrec := Primrec.nat_rec Primrec.id hbody.to₂
  have ht : Primrec₂ repeatTail := by
    apply hrec.of_eq
    intro d n
    induction n with
    | zero => rfl
    | succ n ih => change 4*Nat.pair (Nat.rec _ _ n) d+2 = _;rw [ih];rfl
  have h : Primrec (fun p : Nat×Nat => if p.1=0 then 0 else repeatTail p.2 (p.1-1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (ht.comp Primrec.snd (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)))
  apply h.of_eq
  intro p
  cases p.1 <;> simp [repeatCode]

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  have hhead : Primrec operatorHead := (Primrec.list_getD 0).comp vector_primitive (Primrec.const 1)
  have hea : Primrec (fun p : Nat×Nat×Nat => if p.2.1=0 then p.2.2 else 8*Nat.pair p.1 0+3) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (Primrec.snd.comp Primrec.snd) ((node_primitive 8 3).comp (Primrec.fst.pair (Primrec.const 0)))
  have heb : Primrec (fun p : Nat×Nat×Nat => 8*Nat.pair p.2.1 p.2.2+4) :=
    (node_primitive 8 4).comp Primrec.snd
  have hec : Primrec (fun p : Nat×Nat×Nat => 8*Nat.pair (operatorHead p.2.1) p.2.2+6) :=
    (node_primitive 8 6).comp ((hhead.comp (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
  have he : Primrec₂ eraseCode := fold_primitive _ _ _ hea heb hec
  have hca : Primrec (fun p : Nat×Nat×Nat => if p.2.1=0 then 4*OrdinalSyntax.headClosure p.2.2 else 1) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 4)
        (OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const 1)
  have hcb : Primrec (fun p : Nat×Nat×Nat => 4*Nat.pair p.2.1 p.2.2+2) :=
    (node_primitive 4 2).comp Primrec.snd
  have hcc : Primrec (fun p : Nat×Nat×Nat => 4*Nat.pair (closeOperatorCode p.2.1) p.2.2+3) :=
    (node_primitive 4 3).comp ((operator_close_primitive.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))
  have hc : Primrec closeCode := (fold_primitive _ _ _ hca hcb hcc).comp (Primrec.const 0) Primrec.id
  exact ⟨he,repeat_primitive,operator_close_primitive,hc⟩
end LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Proof
