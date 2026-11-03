module
public import LogicLineages.OrdinalComparison.OriginalGroundCompilerCodeTargets
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodePrimitiveProof
public import LogicLineages.OrdinalComparison.OriginalBudgetCodePrimitiveProof
public import LogicLineages.OrdinalComparison.NumericAccountDataPrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair
private abbrev P := List Nat×Nat×Nat×Nat
private abbrev D := List Nat×List Nat×Nat

private theorem pack_primitive : Primrec₂ packRecords := by
  have hs : Primrec (fun q : (Nat×List Nat)×Nat => SourceAnnotationCode.operatorSource q.2) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hv : Primrec (fun q : (Nat×List Nat)×Nat => SourceAnnotationCode.operatorVector q.2) :=
    Primrec.option_getD.comp (Primrec.decode.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))) (Primrec.const [])
  have hσ : Primrec (fun q : (Nat×List Nat)×Nat => q.1.1) := Primrec.fst.comp Primrec.fst
  exact Primrec.list_map Primrec.snd
    ((Primrec.list_cons.comp hσ (Primrec.list_cons.comp hσ (Primrec.const []))).pair (hs.pair hv)).to₂

private def finish (q : (P×D)×Nat) : Option ((List Nat×Nat×List Nat)×Nat×Nat) :=
  let xs := packRecords q.1.1.2.1 q.1.2.2.1
  (OriginalScaleCompilerCode.compileScaleCode q.1.1.1 q.1.1.2.1 q.1.1.2.2.2 q.2 xs).map
    (fun out => (out,q.2,OriginalScaleCompilerCode.gapCode q.2 xs q.1.2.2.2))

private theorem finish_primitive : Primrec finish := by
  let Q := (P×D)×Nat
  have hp : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have hd : Primrec (fun q : Q => q.1.2) := Primrec.snd.comp Primrec.fst
  have hctx := Primrec.fst.comp hp
  have hσ := Primrec.fst.comp (Primrec.snd.comp hp)
  have hcaller := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hp))
  have hrs := Primrec.fst.comp (Primrec.snd.comp hd)
  have hc := Primrec.snd.comp (Primrec.snd.comp hd)
  have hxs := pack_primitive.comp hσ hrs
  have hgap := OriginalScaleCompilerCode.Proof.primitiveRecursiveAlgorithms.2.2.1.comp
    (Primrec.snd.pair (hxs.pair hc))
  have hcompile := OriginalScaleCompilerCode.Proof.primitiveRecursiveAlgorithms.2.2.2.comp
    (hctx.pair (hσ.pair (hcaller.pair (Primrec.snd.pair hxs))))
  have hout : Primrec (fun q : Q×(List Nat×Nat×List Nat) =>
      (q.2,q.1.2,OriginalScaleCompilerCode.gapCode q.1.2
        (packRecords q.1.1.1.2.1 q.1.1.2.2.1) q.1.1.2.2.2)) :=
    Primrec.snd.pair ((Primrec.snd.comp Primrec.fst).pair (hgap.comp Primrec.fst))
  exact Primrec.option_map hcompile hout.to₂

private def afterAccount (q : P×D) : Option ((List Nat×Nat×List Nat)×Nat×Nat) :=
  (OriginalBudgetCode.budgetCode (q.1.2.1::q.1.1) q.1.2.2.1).bind (fun b => finish (q,b))
private theorem after_account_primitive : Primrec afterAccount := by
  have hctx : Primrec (fun q : P×D => q.1.2.1::q.1.1) :=
    Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.fst)
  have hbody : Primrec (fun q : P×D => q.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.option_bind (OriginalBudgetCode.Proof.primitiveRecursiveAlgorithms.2.2.comp hctx hbody)
    finish_primitive.to₂

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  refine ⟨pack_primitive,?_⟩
  have hctx : Primrec (fun p : P => p.2.1::p.1) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hbody : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcheck : PrimrecPred (fun p : P => SyntaxCode.check (p.2.1::p.1) p.2.2.1 = some 0) :=
    Primrec.eq.comp (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hctx.pair hbody)) (Primrec.const (some 0))
  have hactive : PrimrecPred (fun p : P => TrackedSourceInspectionCode.occursCode 0 p.2.2.1 = true) :=
    Primrec.eq.comp (TrackedSourceInspectionCode.Proof.primitiveRecursiveAlgorithms.1.comp (Primrec.const 0) hbody)
      (Primrec.const true)
  have ha := NumericAccountData.Proof.primitiveRecursiveAlgorithms.2.2.comp hctx hbody
  have h := Primrec.ite hcheck
    (Primrec.ite hactive (Primrec.option_bind ha after_account_primitive.to₂) (Primrec.const none))
    (Primrec.const none)
  apply h.of_eq
  intro p
  unfold compileCode afterAccount finish
  by_cases ht : SyntaxCode.check (p.2.1::p.1) p.2.2.1 = some 0
  · by_cases hf : TrackedSourceInspectionCode.occursCode 0 p.2.2.1 = true
    · simp only [if_pos ht,if_pos hf]
      cases ha : NumericAccountData.sourceAccountCode (p.2.1::p.1) p.2.2.1 with
      | none => rfl
      | some val =>
        cases hb : OriginalBudgetCode.budgetCode (p.2.1::p.1) p.2.2.1 with
        | none => rfl
        | some b =>
          cases hc : OriginalScaleCompilerCode.compileScaleCode p.1 p.2.1 p.2.2.2 b (packRecords p.2.1 val.2.1) <;>
            simp [ha,hb,hc]
    · simp [ht,hf]
  · simp [ht]
end LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Proof
