module
public import LogicLineages.OrdinalComparison.OneUnitCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentPrimitiveProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnitCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem unused_primitive : Primrec unusedCode := by
  have hi := ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
    ((Primrec.const 0).pair ((Primrec.const 1).pair Primrec.id))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp (Primrec.const 0) hi)) (Primrec.const 6)

private theorem first_primitive : Primrec₂ firstCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const 6)

private theorem second_primitive : Primrec₂ secondCode :=
  first_primitive.comp Primrec.fst (unused_primitive.comp Primrec.snd)

private theorem sum_primitive : Primrec (fun xs : List Nat => xs.sum) := by
  have h := Primrec.list_foldr (Primrec.id (α := List Nat)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [id_eq,List.foldr_cons,List.sum_cons] at ih ⊢;rw [ih]

private theorem multiplier_primitive : Primrec₂ multiplierCode := by
  have hpow : Primrec₂ ((· ^ ·) : Nat→Nat→Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hl := SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp (Primrec.fst (α := Nat) (β := List Nat))
  have hs := sum_primitive.comp (Primrec.list_map (Primrec.snd (α := Nat) (β := List Nat))
    (OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.2.2.comp Primrec.snd).to₂)
  exact Primrec.nat_mul.comp (hpow.comp (Primrec.const 2) (Primrec.succ.comp hl)) hs

private theorem compile_primitive : Primrec (fun p : List Nat×Nat×Nat => compileCode p.1 p.2.1 p.2.2) := by
  let P := List Nat×Nat×Nat
  have hσ : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hsrc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hctx : Primrec (fun p : P => p.2.1::p.1) := Primrec.list_cons.comp hσ Primrec.fst
  have ha : Primrec (fun p : P => DefaultSourceAssignment.assignmentCode (p.2.1::p.1) p.2.2) :=
    DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp (hctx.pair hsrc)
  have hb : Primrec (fun q : P×List Nat =>
      DefaultSourceAssignment.assignmentCode (q.1.2.1::q.1.1) (unusedCode q.1.2.2)) :=
    DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp
      ((hctx.comp Primrec.fst).pair (unused_primitive.comp (hsrc.comp Primrec.fst)))
  have hout : Primrec (fun q : (P×List Nat)×List Nat =>
      (multiplierCode q.1.1.2.1 q.1.2,multiplierCode q.1.1.2.1 q.2,
        OrdinalSyntax.headFree (q.1.2.getD 0 0))) := by
    have htype : Primrec (fun q : (P×List Nat)×List Nat => q.1.1.2.1) :=
      hσ.comp (Primrec.fst.comp Primrec.fst)
    have hfirst : Primrec (fun q : (P×List Nat)×List Nat => q.1.2) := Primrec.snd.comp Primrec.fst
    have hfree := OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp
      ((Primrec.list_getD (0 : Nat)).comp hfirst (Primrec.const 0))
    exact (multiplier_primitive.comp htype hfirst).pair
      ((multiplier_primitive.comp htype Primrec.snd).pair hfree)
  exact Primrec.option_bind ha (Primrec.option_bind hb (Primrec.option_some.comp hout).to₂).to₂

private theorem coefficient_primitive : Primrec coefficientCode := by
  have h := Primrec.succ.comp SyntaxCode.Proof.typeLevelPrimitiveRecursive
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) h) (Primrec.const 1)

private theorem constant_primitive : Primrec₂ constantCode := by
  have h := Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.succ.comp (SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp (Primrec.fst (α := Nat) (β := Nat))))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 4) h) Primrec.snd) h

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms :=
  ⟨unused_primitive,first_primitive,second_primitive,multiplier_primitive,compile_primitive,
    coefficient_primitive,constant_primitive⟩
end LogicLineages.OrdinalComparison.Source.OneUnitCode.Proof
