module
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeTargets
public import LogicLineages.OrdinalComparison.SourceAnnotationPartialCodeProof
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Proof
open SourceAnnotationCode
attribute [local irreducible] Nat.sqrt Nat.unpair
private abbrev D := List Nat × Nat
private abbrev S := List Nat × Nat × Nat

private theorem node_prim (tag : Nat) : Primrec (fun p : Nat×Nat => 4*Nat.pair p.1 p.2+tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair) (Primrec.const tag)

private theorem app_prim : Primrec (fun p : Nat×Nat×D×D => appData p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Nat×Nat×D×D
  have hf : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hop := Primrec₂.natPair.comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.encode.comp (Primrec.fst.comp hf)))
  exact (node_prim 3).comp (hop.pair ((node_prim 2).comp ((Primrec.snd.comp hf).pair (Primrec.snd.comp ha))))

attribute [local irreducible] appData

private theorem sum_prim : Primrec (fun xs : List Nat => xs.sum) := by
  have h := Primrec.list_foldr (Primrec.id (α := List Nat)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [id_eq,List.foldr_cons,List.sum_cons] at ih ⊢;rw [ih]

private theorem lambda_prim : Primrec₂ lambdaData := by
  have hb : Primrec (fun p : Nat×D => p.2.2) := Primrec.snd.comp Primrec.snd
  have hv : Primrec (fun p : Nat×D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hfactor := Primrec.nat_mul.comp (Primrec.const 2)
    (sum_prim.comp (Primrec.list_map hv (OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.2.2.comp Primrec.snd).to₂))
  have hp := SourceAnnotationPartialCode.Proof.primitiveRecursive.comp (Primrec.succ.comp Primrec.fst) hb
  have hout : Primrec (fun q : (Nat×D)×Nat =>
      4*Nat.pair (repeatCode (2*((q.1.2.1.map OrdinalSyntax.partialSize).sum)) q.2) (closeCode q.1.2.2)+2) :=
    (node_prim 2).comp
      ((SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.2.1.comp (hfactor.comp Primrec.fst) Primrec.snd).pair
        (SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.2.2.2.comp (hb.comp Primrec.fst)))
  have h := Primrec.option_map hp hout.to₂
  apply h.of_eq
  intro p
  cases hp : SourceAnnotationPartialCode.groundPartialCode (p.1+1) p.2.2 <;>
    simp [lambdaData,hp]

private abbrev AP := Nat×Nat×List Nat×Option D×Option D
private def appMap (q : AP×D) : Option D :=
  q.1.2.2.2.2.map (fun a => (q.1.2.2.1,appData q.1.1 q.1.2.1 q.2 a))

private theorem app_map_prim : Primrec appMap := by
  have ha : Primrec (fun p : AP => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hu : Primrec (fun p : AP => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun q : (AP×D)×D => appData q.1.1.1 q.1.1.2.1 q.1.2 q.2) :=
    app_prim.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  exact Primrec.option_map (ha.comp Primrec.fst) ((hu.comp (Primrec.fst.comp Primrec.fst)).pair hd).to₂

private def appResult (p : AP) : Option D := p.2.2.2.1.bind (fun f => appMap (p,f))

private theorem app_result_prim : Primrec appResult :=
  Primrec.option_bind (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) app_map_prim.to₂

private def lamResult (p : Nat×List Nat×Option D) : Option D := do
  let body ← p.2.2
  let d ← lambdaData p.1 body
  pure (p.2.1,d)

private theorem lam_result_prim : Primrec lamResult := by
  let P := Nat×List Nat×Option D
  have hp := lambda_prim.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd : Primrec (fun p : P×D => p.2))
  have hu : Primrec (fun q : (P×D)×Nat => q.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have h := Primrec.option_bind (Primrec.snd.comp Primrec.snd)
    (Primrec.option_map hp (hu.pair Primrec.snd).to₂).to₂
  apply h.of_eq
  intro p
  cases hb : p.2.2 <;> simp [lamResult,hb,Option.map_eq_bind]

private abbrev P := S × List (Option D) × Nat × List Nat
private def finish (p : P) : Option D :=
  if TrackedSourceInspectionCode.occursCode p.1.2.1 p.1.2.2 = false then some (p.2.2.2,4*(p.2.2.2.getD 0 0))
  else if p.1.2.2%8=0 then if p.1.2.2/8=p.1.2.1 then some (p.2.2.2,1) else none
  else if p.1.2.2%8=5 then (SyntaxCode.check p.1.1 (p.1.2.2/8).unpair.2).bind (fun argType =>
    if argType=0 then appResult (p.2.2.1,(p.1.2.2/8).unpair.1,p.2.2.2,p.2.1.getD 0 none,p.2.1.getD 1 none) else none)
  else if p.1.2.2%8=6 then if (p.1.2.2/8).unpair.1=0 then
    lamResult (p.1.2.1,p.2.2.2,p.2.1.getD 0 none) else none
  else none

private theorem finish_prim : Primrec finish := by
  have hs : Primrec (fun p : P => p.1) := Primrec.fst
  have hctx : Primrec (fun p : P => p.1.1) := Primrec.fst.comp hs
  have ht : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp hs)
  have hn : Primrec (fun p : P => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp hs)
  have hu : Primrec (fun p : P => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have har : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrows : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hg (i : Nat) := (Primrec.list_getD (none : Option D)).comp hrows (Primrec.const i)
  have htag := Primrec.nat_mod.comp hn (Primrec.const 8)
  have hpay := Primrec.nat_div.comp hn (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have hf := TrackedSourceInspectionCode.Proof.primitiveRecursiveAlgorithms.1.comp ht hn
  have hfree := Primrec.option_some.comp (hu.pair (Primrec.nat_mul.comp (Primrec.const 4)
    ((Primrec.list_getD 0).comp hu (Primrec.const 0))))
  have happ0 := app_result_prim.comp (har.pair (hl.pair (hu.pair ((hg 0).pair (hg 1)))))
  have happ : Primrec (fun p : P => (SyntaxCode.check p.1.1 (p.1.2.2/8).unpair.2).bind (fun a =>
      if a=0 then appResult (p.2.2.1,(p.1.2.2/8).unpair.1,p.2.2.2,p.2.1.getD 0 none,p.2.1.getD 1 none) else none)) :=
    Primrec.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hctx.pair hr))
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (happ0.comp Primrec.fst) (Primrec.const none)).to₂
  have hlam := lam_result_prim.comp (ht.pair (hu.pair (hg 0)))
  exact Primrec.ite (Primrec.eq.comp hf (Primrec.const false)) hfree
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp hpay ht) (Primrec.option_some.comp (hu.pair (Primrec.const 1))) (Primrec.const none))
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) happ
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6))
      (Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) hlam (Primrec.const none)) (Primrec.const none))))

private def prepare (p : S×List (Option D)) : Option D := do
  let τ ← SyntaxCode.check p.1.1 p.1.2.2
  let arity ← TrackedSourceInspectionCode.arityCode τ
  let u ← DefaultSourceAssignment.assignmentCode p.1.1 p.1.2.2
  finish (p.1,p.2,arity,u)

private theorem prepare_prim : Primrec prepare := by
  let Q := S×List (Option D)
  have hs : Primrec (fun p : Q => p.1) := Primrec.fst
  have hctx := Primrec.fst.comp hs
  have hn := Primrec.snd.comp (Primrec.snd.comp hs)
  apply Primrec.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hctx.pair hn))
  apply Primrec.option_bind (TrackedSourceInspectionCode.Proof.primitiveRecursiveAlgorithms.2.comp Primrec.snd)
  have ha : Primrec (fun q : (Q×Nat)×Nat => DefaultSourceAssignment.assignmentCode q.1.1.1.1 q.1.1.1.2.2) :=
    DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive.comp
      ((hctx.comp (Primrec.fst.comp Primrec.fst)).pair (hn.comp (Primrec.fst.comp Primrec.fst)))
  apply Primrec.option_bind ha
  exact finish_prim.comp
    ((hs.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))

theorem primitiveRecursive : Targets.PrimitiveRecursive := by
  let children : S → List S := fun s =>
    if s.2.2%8=5 then [(s.1,s.2.1,(s.2.2/8).unpair.1),(s.1,s.2.1,(s.2.2/8).unpair.2)]
    else if s.2.2%8=6 then [(0::s.1,s.2.1+1,(s.2.2/8).unpair.2)] else []
  have hn : Primrec (fun s : S => s.2.2) := Primrec.snd.comp Primrec.snd
  have hi : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have htag := Primrec.nat_mod.comp hn (Primrec.const 8)
  have hpay := Primrec.nat_div.comp hn (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (i : Nat) := Primrec.eq.comp htag (Primrec.const i)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair (hi.pair hl))
      (Primrec.list_cons.comp (Primrec.fst.pair (hi.pair hr)) (Primrec.const [])))
    (Primrec.ite (ht 6) (Primrec.list_cons.comp
      ((Primrec.list_cons.comp (Primrec.const 0) Primrec.fst).pair ((Primrec.succ.comp hi).pair hr)) (Primrec.const []))
      (Primrec.const []))
  have ha : Primrec₂ (fun (s : S) (rs : List (Option D)) => some (prepare (s,rs))) := Primrec.option_some.comp prepare_prim
  apply Primrec.nat_omega_rec' (fun s : S => buildCode s.1 s.2.1 s.2.2) hn hc ha
  · intro s t hm
    change t.2.2<s.2.2
    by_cases h5 : s.2.2%8=5
    · have hd : s.2.2/8<s.2.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2.2%8=6
      · have hd : s.2.2/8<s.2.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hm
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hm
  · intro s
    conv_rhs => rw [buildCode]
    have ht : s.2.2%8=0 ∨ s.2.2%8=1 ∨ s.2.2%8=2 ∨ s.2.2%8=3 ∨ s.2.2%8=4 ∨ s.2.2%8=5 ∨ s.2.2%8=6 ∨ s.2.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;>
      simp [children,prepare,finish,h,appResult,appMap,lamResult,Option.bind_assoc,Option.map_eq_bind]
end LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Proof
