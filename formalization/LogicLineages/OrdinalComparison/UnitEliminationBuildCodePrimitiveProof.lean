module
public import LogicLineages.OrdinalComparison.UnitEliminationBuildCodeTargets
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeProof
public import LogicLineages.OrdinalComparison.SelectedBinderCodePrimitiveProof
public import LogicLineages.OrdinalComparison.OneUnitCodePrimitiveProof
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodePrimitiveProof
public import LogicLineages.OrdinalComparison.UnitEliminationTreeCodeFoldProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckPrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Proof
open UnitEliminationTreeCode
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] UnitContextSelectionCode.selectCode
  OneUnitCode.compileCode OneUnitCode.firstCode OneUnitCode.secondCode
  OneUnitCode.coefficientCode OneUnitCode.constantCode UnitGroundBlockCode.buildCode
  leafCode freeCode activeCode buildCode
private abbrev S := Nat×List Nat×Nat
private abbrev R := UnitContextSelectionCode.Split
private abbrev D := Nat×Nat×Bool
private def context (r : R) : List Nat := r.1++r.2.2
private def moved (s : S) (r : R) : Nat := SelectedBinderCode.sourceCode 0 r.1.length s.2.2
private def chosen (s : S) : R := (UnitContextSelectionCode.selectCode s.2.1).getD ([],0,[])
private def children (s : S) : List S :=
  if s.1=0 then [] else
    let r := chosen s
    [(s.1-1,context r,OneUnitCode.firstCode r.2.1 (moved s r)),
     (s.1-1,context r,OneUnitCode.secondCode r.2.1 (moved s r))]
private def freeMeta (r : R) (d : D) : Nat := Encodable.encode (r.1,r.2.2,r.2.1,d.1)
private def activeMeta (τ : Nat) (r : R) (d : D) : Nat :=
  Encodable.encode (r.1,r.2.2,r.2.1,OneUnitCode.coefficientCode τ,d.1,d.2.1,OneUnitCode.constantCode τ d.2.1)
private def combine (τ : Nat) (r : R) (d : D) (qs : List (Option Nat)) : Option Nat := do
  let q ← qs.getD 0 none
  if d.2.2 then pure (freeCode (freeMeta r d) q)
  else
    let t ← qs.getD 1 none
    pure (activeCode (activeMeta τ r d) q t)
private def assemble (s : S) (qs : List (Option Nat)) : Option (Option Nat) := some
  (if s.1=0 then none else do
    let τ ← SyntaxCode.check s.2.1 s.2.2
    match UnitContextSelectionCode.selectCode s.2.1 with
    | none => pure (leafCode (Encodable.encode (UnitGroundBlockCode.buildCode s.2.1.length τ s.2.2)))
    | some r => do
      let d ← OneUnitCode.compileCode (context r) r.2.1 (moved s r)
      combine τ r d qs)

private theorem context_primitive : Primrec context :=
  Primrec.list_append.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
private theorem moved_primitive : Primrec₂ moved := by
  have hl : Primrec (fun p : S×R => p.2.1.length) := Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  have hs : Primrec (fun p : S×R => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact SelectedBinderCode.Proof.primitiveRecursiveAlgorithms.2.1.comp
    ((Primrec.const 0).pair (hl.pair hs))
private theorem chosen_primitive : Primrec chosen :=
  Primrec.option_getD.comp
    (UnitContextSelectionCode.Proof.primitiveRecursiveSelection.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.const ([],0,[]))
private theorem children_primitive : Primrec children := by
  have hr := chosen_primitive
  have hn : Primrec (fun s : S=>s.1-1) := Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)
  have hctx := context_primitive.comp hr
  have htype := Primrec.fst.comp (Primrec.snd.comp hr)
  have ha := moved_primitive.comp Primrec.id hr
  have hfirst := OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.1.comp htype ha
  have hsecond := OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.2.1.comp htype ha
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst : Primrec (fun s : S=>s.1)) (Primrec.const 0))
    (Primrec.const []) (Primrec.list_cons.comp (hn.pair (hctx.pair hfirst))
      (Primrec.list_cons.comp (hn.pair (hctx.pair hsecond)) (Primrec.const [])))

private abbrev C := Nat×R×D×List (Option Nat)
private theorem free_meta_primitive : Primrec (fun p : C=>freeMeta p.2.1 p.2.2.1) := by
  have hr : Primrec (fun p : C=>p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : C=>p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.encode.comp ((Primrec.fst.comp hr).pair
    ((Primrec.snd.comp (Primrec.snd.comp hr)).pair
      ((Primrec.fst.comp (Primrec.snd.comp hr)).pair (Primrec.fst.comp hd))))
private theorem active_meta_primitive : Primrec (fun p : C=>activeMeta p.1 p.2.1 p.2.2.1) := by
  have ht : Primrec (fun p : C=>p.1) := Primrec.fst
  have hr : Primrec (fun p : C=>p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : C=>p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hdp := Primrec.fst.comp (Primrec.snd.comp hd)
  have hcoef := OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.1.comp ht
  have hc := OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.2.2.comp ht hdp
  exact Primrec.encode.comp ((Primrec.fst.comp hr).pair
    ((Primrec.snd.comp (Primrec.snd.comp hr)).pair
      ((Primrec.fst.comp (Primrec.snd.comp hr)).pair (hcoef.pair
        ((Primrec.fst.comp hd).pair (hdp.pair hc))))))
attribute [local irreducible] freeMeta activeMeta

private theorem combine_primitive : Primrec (fun p : C=>combine p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hqs : Primrec (fun p : C=>p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hfree : Primrec (fun p : C=>p.2.2.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hzero := (Primrec.list_getD (none : Option Nat)).comp hqs (Primrec.const 0)
  have hone : Primrec (fun p : C×Nat=>p.1.2.2.2.getD 1 none) :=
    (Primrec.list_getD (none : Option Nat)).comp (hqs.comp Primrec.fst) (Primrec.const 1)
  have hf : Primrec (fun p : C×Nat=>some (freeCode (freeMeta p.1.2.1 p.1.2.2.1) p.2)) :=
    Primrec.option_some.comp (UnitEliminationTreeCode.Proof.effectiveConstructorsAndFold.2.1.comp
      (free_meta_primitive.comp Primrec.fst) Primrec.snd)
  have ha : Primrec (fun p : (C×Nat)×Nat=>some (activeCode
      (activeMeta p.1.1.1 p.1.1.2.1 p.1.1.2.2.1) p.1.2 p.2)) :=
    Primrec.option_some.comp (UnitEliminationTreeCode.Proof.effectiveConstructorsAndFold.2.2.1.comp
      ((active_meta_primitive.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  apply (Primrec.option_bind hzero
    (Primrec.cond (hfree.comp Primrec.fst) hf (Primrec.option_bind hone ha.to₂)).to₂).of_eq
  intro p
  cases h : p.2.2.1.2.2 <;> simp [combine,h]

private abbrev P := S×List (Option Nat)
private abbrev V := P×Nat
private theorem selected_primitive : Primrec (fun p : V×R=>
    (OneUnitCode.compileCode (context p.2) p.2.2.1 (moved p.1.1.1 p.2)).bind
      (fun d=>combine p.1.2 p.2 d p.1.1.2)) := by
  have hs : Primrec (fun p : V×R=>p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun p : V×R=>p.2) := Primrec.snd
  have hc := OneUnitCode.Proof.primitiveRecursiveAlgorithms.2.2.2.2.1.comp
    ((context_primitive.comp hr).pair ((Primrec.fst.comp (Primrec.snd.comp hr)).pair
      (moved_primitive.comp hs hr)))
  have hout : Primrec (fun p : (V×R)×D=>combine p.1.1.2 p.1.2 p.2 p.1.1.1.2) :=
    combine_primitive.comp ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.pair
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
  exact Primrec.option_bind hc hout.to₂
private theorem after_check_primitive : Primrec (fun p : V=>
    match UnitContextSelectionCode.selectCode p.1.1.2.1 with
    | none => some (leafCode (Encodable.encode (UnitGroundBlockCode.buildCode p.1.1.2.1.length p.2 p.1.1.2.2)))
    | some r => (OneUnitCode.compileCode (context r) r.2.1 (moved p.1.1 r)).bind
      (fun d=>combine p.2 r d p.1.2)) := by
  have hctx : Primrec (fun p : V=>p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hsrc : Primrec (fun p : V=>p.1.1.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hblock := UnitGroundBlockCode.Proof.effectiveAlgorithms.2.2.2.1.comp
    ((Primrec.list_length.comp hctx).pair (Primrec.snd.pair hsrc))
  have hleaf := Primrec.option_some.comp
    (UnitEliminationTreeCode.Proof.effectiveConstructorsAndFold.1.comp (Primrec.encode.comp hblock))
  apply (Primrec.option_casesOn (UnitContextSelectionCode.Proof.primitiveRecursiveSelection.comp hctx)
    hleaf selected_primitive.to₂).of_eq
  intro p
  cases h : UnitContextSelectionCode.selectCode p.1.1.2.1 <;> simp [h]
private theorem assemble_primitive : Primrec₂ assemble := by
  have hfuel : Primrec (fun p : P=>p.1.1) := Primrec.fst.comp Primrec.fst
  have hctx : Primrec (fun p : P=>p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hsrc : Primrec (fun p : P=>p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.option_some.comp (Primrec.ite (Primrec.eq.comp hfuel (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_bind (SyntaxCode.Proof.checkPrimitiveRecursive.comp (hctx.pair hsrc)) after_check_primitive.to₂))

private theorem build_primitive : Primrec (fun p : S=>buildCode p.1 p.2.1 p.2.2) := by
  apply Primrec.nat_omega_rec' (fun p : S=>buildCode p.1 p.2.1 p.2.2) Primrec.fst children_primitive assemble_primitive
  · intro s t ht
    by_cases h : s.1=0
    · simp [children,h] at ht
    · simp only [children,if_neg h,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl|rfl <;> change s.1-1<s.1 <;> omega
  · rintro ⟨fuel,Γ,src⟩
    cases fuel with
    | zero => simp [assemble,buildCode]
    | succ fuel =>
      simp only [assemble,Nat.succ_ne_zero,if_false]
      rw [buildCode]
      cases hc : SyntaxCode.check Γ src with
      | none => simp [hc]
      | some τ =>
        cases hs : UnitContextSelectionCode.selectCode Γ with
        | none => simp [hc,hs]
        | some r =>
          rcases r with ⟨left,σ,right⟩
          cases hd : OneUnitCode.compileCode (left++right) σ (SelectedBinderCode.sourceCode 0 left.length src) with
          | none => simp [hc,hs,context,moved,hd]
          | some d =>
            simp only [hc,hs,context,moved,hd,Option.bind_some]
            simp only [combine,children,chosen,Nat.succ_ne_zero,if_false,hs,Option.getD_some,
              Nat.succ_sub_one,List.map_cons,List.map_nil,List.getD_cons_zero,List.getD_cons_succ,
              context,moved,freeMeta,activeMeta]

theorem primitiveRecursiveSymbolicCompiler : Targets.PrimitiveRecursiveSymbolicCompiler := by
  refine ⟨build_primitive,?_⟩
  exact build_primitive.comp ((Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)).pair
    (Primrec.fst.pair Primrec.snd))
end LogicLineages.OrdinalComparison.Source.UnitEliminationBuildCode.Proof
