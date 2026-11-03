module
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeTargets
public import LogicLineages.OrdinalComparison.NumericUnaryChainPrimitiveProof
public import LogicLineages.OrdinalComparison.NumericCarrierDataPrimitiveProof
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Proof
open NumericUnaryChain
attribute [local irreducible] Nat.sqrt Nat.unpair
private abbrev P := List Nat×Nat×Nat

private def callerVector (q : P×Nat) : Option RawOperator :=
  (DefaultSourceAssignment.assignmentCode q.1.1 q.1.2.2).map (fun v =>
    ([],NumericCarrierData.saturateSource (q.2-1) q.1.2.2,NumericCarrierData.saturateVector (q.2-1) v))
private theorem caller_vector_primitive : Primrec callerVector := by
  have hctx : Primrec (fun q : P×Nat => q.1.1) := Primrec.fst.comp Primrec.fst
  have hsrc : Primrec (fun q : P×Nat => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hr : Primrec (fun q : P×Nat => q.2-1) := Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hs := NumericCarrierData.Proof.primitiveRecursiveAlgorithms.2.2.1.comp hr hsrc
  have hv : Primrec (fun q : (P×Nat)×List Nat => NumericCarrierData.saturateVector (q.1.2-1) q.2) :=
    NumericCarrierData.Proof.primitiveRecursiveAlgorithms.2.2.2.1.comp (hr.comp Primrec.fst) Primrec.snd
  exact Primrec.option_map
    (DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp (hctx.pair hsrc))
    ((Primrec.const ([] : List Nat)).pair ((hs.comp Primrec.fst).pair hv)).to₂

private def callerArity (p : P) : Option RawOperator :=
  (TrackedSourceInspectionCode.arityCode p.2.1).bind (fun r => if r=0 then none else callerVector (p,r))
private theorem caller_arity_primitive : Primrec callerArity :=
  Primrec.option_bind
    (TrackedSourceInspectionCode.Proof.primitiveRecursiveAlgorithms.2.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none) caller_vector_primitive).to₂

private theorem caller_primitive : Primrec (fun p : P => callerCode p.1 p.2.1 p.2.2) := by
  have hctx : Primrec (fun p : P => p.1) := Primrec.fst
  have hs : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have h := Primrec.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hctx.pair hn))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (hs.comp Primrec.fst))
      (caller_arity_primitive.comp Primrec.fst) (Primrec.const none)).to₂
  apply h.of_eq
  intro p
  cases hc : SyntaxCode.check p.1 p.2.2 <;>
    simp [callerCode,callerArity,callerVector,hc]
  cases ha : DefaultSourceAssignment.assignmentCode p.1 p.2.2 <;> simp [ha]

private theorem scale_primitive : Primrec (fun b : Nat => 2^b) := by
  have hs : Primrec (fun p : Nat×Nat×Nat => p.2.2*2) :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)
  have h := Primrec.nat_rec (Primrec.const (1 : Nat) (α := Nat)) hs.to₂
  have hh : Primrec₂ (fun _ : Nat => fun n : Nat => 2^n) := by
    apply h.of_eq
    intro x n
    induction n with
    | zero => rfl
    | succ n ih => change (Nat.rec _ _ n)*2 = _;rw [ih,Nat.pow_succ]
  exact hh.comp (Primrec.const 0) Primrec.id

private theorem replicate_primitive {α : Type} [Primcodable α] : Primrec₂ (fun n : Nat => fun x : α => List.replicate n x) := by
  have hs : Primrec (fun p : α×Nat×List α => p.1::p.2.2) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec (Primrec.const ([] : List α) (α := α)) hs.to₂
  have hh : Primrec₂ (fun x : α => fun n : Nat => List.replicate n x) := by
    apply h.of_eq
    intro x n
    induction n with
    | zero => rfl
    | succ n ih => change x::Nat.rec _ _ n = _;rw [ih,List.replicate_succ]
  exact hh.comp Primrec.snd Primrec.fst

private theorem paid_primitive : Primrec (fun p : Nat×List RawOperator×RawOperator => paidCode p.1 p.2.1 p.2.2) :=
  Primrec.list_append.comp
    (Primrec.list_flatten.comp (replicate_primitive.comp (scale_primitive.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
    (replicate_primitive.comp (scale_primitive.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

private theorem gap_primitive : Primrec (fun p : Nat×List RawOperator×Nat => gapCode p.1 p.2.1 p.2.2) :=
  Primrec.nat_sub.comp (Primrec.nat_mul.comp (scale_primitive.comp Primrec.fst)
    (Primrec.nat_sub.comp (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.const 3))) (Primrec.const 1)

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  refine ⟨caller_primitive,paid_primitive,gap_primitive,?_⟩
  let Q := List Nat×Nat×Nat×Nat×List RawOperator
  have hctx : Primrec (fun p : Q => p.1) := Primrec.fst
  have hs : Primrec (fun p : Q => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Q => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : Q => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hx : Primrec (fun p : Q => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hout : Primrec (fun q : Q×RawOperator => NumericUnaryChain.compileCode q.1.1 (paidCode q.1.2.2.2.1 q.1.2.2.2.2 q.2)) :=
    NumericUnaryChain.Proof.primitiveRecursiveAlgorithms.2.2.2.comp (hctx.comp Primrec.fst)
      (paid_primitive.comp ((hb.comp Primrec.fst).pair ((hx.comp Primrec.fst).pair Primrec.snd)))
  exact Primrec.option_bind (caller_primitive.comp (hctx.pair (hs.pair hn))) hout.to₂
end LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Proof
