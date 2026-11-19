module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionCodePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageStatementChecks
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadStatementChecks
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.StandardControlCurrent.PolicyAssignmentStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open RawSourceDAG (Code)

private theorem addP {P : Type} [Primcodable P] {a b : P → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => a x + b x) :=
  Primrec.nat_add.comp ha hb

private theorem mulP {P : Type} [Primcodable P] {a b : P → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => a x * b x) :=
  Primrec.nat_mul.comp ha hb

theorem equationPrimitive : Primrec₂ equation := by
  let Q := Nat × Coefficients
  have hq : Primrec (fun x : Q => x.1) := Primrec.fst
  have hb : Primrec (fun x : Q => x.2) := Primrec.snd
  have ht := Primrec.snd.comp hb
  have hd := Primrec.fst.comp hb
  have hd' := Primrec.fst.comp ht
  have hflag := Primrec.snd.comp ht
  have k := mulP (Primrec.const 2) (addP hq (Primrec.const 1))
  have c := addP (mulP (mulP (Primrec.const 4) k) hd') k
  have p₀ := addP k (Primrec.const 1)
  have hfree : Primrec (fun x : Q => ((1,0,0,x.2.1+1,x.2.1) : LinearCode)) :=
    (Primrec.const 1).pair ((Primrec.const 0).pair ((Primrec.const 0).pair
      ((addP hd (Primrec.const 1)).pair hd)))
  have hactive : Primrec (fun x : Q => (((2*(x.1+1)+1)*x.2.2.1,
      x.2.1*(4*(2*(x.1+1))*x.2.2.1+2*(x.1+1)),x.2.1,
      (2*(x.1+1)+1)*(x.2.2.1-x.2.1),0) : LinearCode)) :=
    (mulP p₀ hd').pair ((mulP hd c).pair (hd.pair
      ((mulP p₀ (Primrec.nat_sub.comp hd' hd)).pair (Primrec.const 0))))
  exact (Primrec.cond hflag hfree hactive).of_eq (fun x => by
    unfold equation
    cases x.2.2.2 <;> rfl)

private theorem lambdaPrimitive : Primrec₂ lambdaCode :=
  addP (mulP (Primrec.const 8) Primrec₂.natPair) (Primrec.const 6)

private theorem slotPrimitive : Primrec₂ slotIndex := by
  let Q := Nat × Nat
  have i : Primrec (fun x : Q => x.1) := Primrec.fst
  have j : Primrec (fun x : Q => x.2) := Primrec.snd
  exact Primrec.ite (Primrec.nat_lt.comp j i) (addP j (Primrec.const 1))
    (Primrec.ite (Primrec.eq.comp j i) (Primrec.const 0) j)

private theorem tablePrimitive : Primrec₂ selectedTable := by
  let Q := Nat × List Nat
  have h : Primrec (fun x : Q => List.range x.2.length) :=
    Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)
  exact Primrec.list_map h (slotPrimitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

private theorem movePrimitive : Primrec₂ moveCode := by
  let Q := Nat × Code
  have d : Primrec (fun x : Q => x.2) := Primrec.snd
  have i : Primrec (fun x : Q => x.1) := Primrec.fst
  have Γ := Primrec.fst.comp d
  have before := Primrec.list_take.comp i Γ
  have after := Primrec.list_drop.comp (addP i (Primrec.const 1)) Γ
  have rest := Primrec.list_append.comp before after
  have table := tablePrimitive.comp i Γ
  have ctx := Primrec.list_cons.comp (Primrec.snd : Primrec (fun x : Q × Nat => x.2))
    (rest.comp Primrec.fst)
  have hr := RawSourceDAG.Operations.rename_code_primitive.comp
    (ctx.pair ((table.comp Primrec.fst).pair (d.comp Primrec.fst)))
  exact Primrec.option_bind (Primrec.list_getElem?.comp Γ i)
    (Primrec.option_some.comp hr).to₂

private theorem codedSizePrimitive : Primrec₂ codedMultiplier := by
  let Q := Nat × List Nat
  have hty : Primrec (fun x : Q => x.1) := Primrec.fst
  have hxs : Primrec (fun x : Q => x.2) := Primrec.snd
  have hPow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hp := hPow.comp (Primrec.const 2)
    (addP (SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp hty) (Primrec.const 1))
  have hs := LogicLineages.OrdinalComparison.StatementChecks.fixed_ordinalSyntaxHeadOperationsPrimitiveRecursive.2.2
  have hm := Primrec.list_map hxs (hs.comp (Primrec.snd : Primrec (fun x : Q × Nat => x.2))).to₂
  have hfold : Primrec (fun x : Q × (Nat × Nat) => x.2) := Primrec.snd
  have htotal : Primrec (fun x : Q => (x.2.map OrdinalSyntax.partialSize).sum) :=
    Primrec.list_foldr hm (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp hfold) (Primrec.snd.comp hfold)).to₂
  exact mulP hp htotal

private abbrev Finish := HeadInput × Nat × Nat × Nat × List Nat × List Nat × Nat

private def finish (x : Finish) : Packet :=
  let σ := x.2.1
  let τ := x.2.2.1
  let u := x.2.2.2.1
  let h := x.2.2.2.2.1
  let h' := x.2.2.2.2.2.1
  let h₀ := x.2.2.2.2.2.2
  let d : Coefficients := (codedMultiplier σ h,codedMultiplier σ h',OrdinalSyntax.headFree h₀)
  (lambdaCode σ x.1.2,if d.2.2 then none else some (lambdaCode σ u),d,
    equation (SyntaxCode.typeLevel τ) d)

private theorem finishPrimitive : Primrec finish := by
  have t₁ : Primrec (fun x : Finish => x.2) := Primrec.snd
  have t₂ := Primrec.snd.comp t₁
  have t₃ := Primrec.snd.comp t₂
  have t₄ := Primrec.snd.comp t₃
  have t₅ := Primrec.snd.comp t₄
  have hσ := Primrec.fst.comp t₁
  have hτ := Primrec.fst.comp t₂
  have hu := Primrec.fst.comp t₃
  have hv := Primrec.fst.comp t₄
  have hv' := Primrec.fst.comp t₅
  have hv₀ := Primrec.snd.comp t₅
  have hf := LogicLineages.OrdinalComparison.StatementChecks.fixed_ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp hv₀
  have hdata : Primrec (fun x : Finish => ((codedMultiplier x.2.1 x.2.2.2.2.1,
      codedMultiplier x.2.1 x.2.2.2.2.2.1,OrdinalSyntax.headFree x.2.2.2.2.2.2) : Coefficients)) :=
    (codedSizePrimitive.comp hσ hv).pair ((codedSizePrimitive.comp hσ hv').pair hf)
  have ha := lambdaPrimitive.comp hσ (Primrec.snd.comp (Primrec.fst : Primrec (fun x : Finish => x.1)))
  have hb : Primrec (fun x : Finish =>
      if OrdinalSyntax.headFree x.2.2.2.2.2.2 then none else some (lambdaCode x.2.1 x.2.2.2.1)) :=
    (Primrec.cond hf (Primrec.const none) (Primrec.option_some.comp (lambdaPrimitive.comp hσ hu))).of_eq
      (fun x => by cases OrdinalSyntax.headFree x.2.2.2.2.2.2 <;> rfl)
  exact ha.pair (hb.pair (hdata.pair (equationPrimitive.comp
    (SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp hτ) hdata)))

private abbrev Stage (A : Type) := HeadInput × Nat × Nat × A

private theorem headComputable (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) :
    Computable (compileHead p) := by
  have assign := (PolicyAssignmentStatementChecks.full.2.2.2 p hp).2
  have tree := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.2
  have finishH : Computable (fun x : Stage (Nat × List Nat × List Nat) =>
      x.2.2.2.2.1.head?.bind (fun h₀ => some (finish (x.1,x.2.1,x.2.2.1,x.2.2.2.1,
        x.2.2.2.2.1,x.2.2.2.2.2,h₀)))) := by
    let Q := Stage (Nat × List Nat × List Nat)
    have h : Computable (fun x : Q => x.2) := Computable.snd
    have h' := Computable.snd.comp h
    have h'' := Computable.snd.comp h'
    have hd := Computable.snd.comp h''
    have hd' := Computable.snd.comp hd
    have f : Computable (fun y : Q × Nat => finish (y.1.1,y.1.2.1,y.1.2.2.1,
        y.1.2.2.2.1,y.1.2.2.2.2.1,y.1.2.2.2.2.2,y.2)) :=
      finishPrimitive.to_comp.comp ((Computable.fst.comp Computable.fst).pair
        (((Computable.fst.comp h).comp Computable.fst).pair
          (((Computable.fst.comp h').comp Computable.fst).pair
            (((Computable.fst.comp h'').comp Computable.fst).pair
              (((Computable.fst.comp hd).comp Computable.fst).pair
                ((hd'.comp Computable.fst).pair Computable.snd))))))
    exact Computable.option_bind (Primrec.list_head?.to_comp.comp (Computable.fst.comp hd))
      (Computable.option_some.comp f).to₂
  have secondH : Computable (fun x : Stage (Nat × List Nat) =>
      (PolicyAssignment.assignmentCode p x.1.1 x.2.2.2.1).bind (fun h' =>
        x.2.2.2.2.head?.bind (fun h₀ => some (finish
          (x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2,h',h₀))))) := by
    let Q := Stage (Nat × List Nat)
    have hx : Computable (fun x : Q => x.1) := Computable.fst
    have ht : Computable (fun x : Q => x.2) := Computable.snd
    have hk := Computable.snd.comp ht
    have hv := Computable.snd.comp hk
    have hA := assign.comp ((Computable.fst.comp hx).pair (Computable.fst.comp hv))
    have extend : Computable (fun y : Q × List Nat =>
        ((y.1.1,y.1.2.1,y.1.2.2.1,y.1.2.2.2.1,y.1.2.2.2.2,y.2) :
          Stage (Nat × List Nat × List Nat))) :=
      (hx.comp Computable.fst).pair (((Computable.fst.comp ht).comp Computable.fst).pair
        (((Computable.fst.comp hk).comp Computable.fst).pair
          (((Computable.fst.comp hv).comp Computable.fst).pair
            (((Computable.snd.comp hv).comp Computable.fst).pair Computable.snd))))
    exact Computable.option_bind hA (finishH.comp extend).to₂
  have firstH : Computable (fun x : Stage Nat =>
      (PolicyAssignment.assignmentCode p x.1.1 x.1.2).bind (fun h =>
        (PolicyAssignment.assignmentCode p x.1.1 x.2.2.2).bind (fun h' =>
          h.head?.bind (fun h₀ => some (finish (x.1,x.2.1,x.2.2.1,x.2.2.2,h,h',h₀)))))) := by
    let Q := Stage Nat
    have hx : Computable (fun x : Q => x.1) := Computable.fst
    have ht : Computable (fun x : Q => x.2) := Computable.snd
    have hk := Computable.snd.comp ht
    have extend : Computable (fun y : Q × List Nat =>
        ((y.1.1,y.1.2.1,y.1.2.2.1,y.1.2.2.2,y.2) : Stage (Nat × List Nat))) :=
      (hx.comp Computable.fst).pair (((Computable.fst.comp ht).comp Computable.fst).pair
        (((Computable.fst.comp hk).comp Computable.fst).pair
          (((Computable.snd.comp hk).comp Computable.fst).pair Computable.snd)))
    exact Computable.option_bind (assign.comp hx) (secondH.comp extend).to₂
  let K := HeadInput × Nat × Nat
  have context : Computable (fun x : K => x.1.1) := Computable.fst.comp Computable.fst
  have main : Computable (fun x : K =>
      (CurrentTreeInputCoverage.compile x.1.1 x.1.2).bind (fun d =>
        let u := lambdaCode 0 (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1 d))
        (PolicyAssignment.assignmentCode p x.1.1 x.1.2).bind (fun h =>
          (PolicyAssignment.assignmentCode p x.1.1 u).bind (fun h' =>
            h.head?.bind (fun h₀ => some (finish (x.1,x.2.1,x.2.2,u,h,h',h₀))))))) := by
    have treeBody : Computable (fun y : K × Code => lambdaCode 0
        (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1 y.2))) :=
      lambdaPrimitive.to_comp.comp (Computable.const 0)
        (CurrentTreeCode.effective.to_comp.comp
          (CurrentDecision.liftCodePrimitive.to_comp.comp (Computable.const 1) Computable.snd))
    have z : Computable (fun y : K × Code => y.1.2) := Computable.snd.comp Computable.fst
    have extend : Computable (fun y : K × Code =>
        ((y.1.1,y.1.2.1,y.1.2.2,lambdaCode 0
          (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1 y.2))) : Stage Nat)) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp z).pair ((Computable.snd.comp z).pair treeBody))
    exact Computable.option_bind (tree.comp context (Computable.snd.comp Computable.fst))
      (firstH.comp extend).to₂
  let H := HeadInput × Nat
  let check := fun x : H => SyntaxCode.check x.1.1 x.1.2
  have hCheck : Computable check :=
    SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp.comp Computable.fst
  have checked : Computable (fun x : H =>
      (check x).bind (fun τ =>
        (CurrentTreeInputCoverage.compile x.1.1 x.1.2).bind (fun d =>
          let u := lambdaCode 0 (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1 d))
          (PolicyAssignment.assignmentCode p x.1.1 x.1.2).bind (fun h =>
            (PolicyAssignment.assignmentCode p x.1.1 u).bind (fun h' =>
              h.head?.bind (fun h₀ => some (finish (x.1,x.2,τ,u,h,h',h₀)))))))) :=
    Computable.option_bind hCheck
      (main.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂
  have guard : Computable (fun x : H => decide (0 < SyntaxCode.typeLevel x.2)) :=
    (Primrec.nat_lt.comp (Primrec.const 0)
      (SyntaxCode.Proof.typeLevelPrimitiveRecursive.comp Primrec.snd)).decide.to_comp
  have body : Computable (fun x : H => if 0 < SyntaxCode.typeLevel x.2 then
      (check x).bind (fun τ =>
        (CurrentTreeInputCoverage.compile x.1.1 x.1.2).bind (fun d =>
          let u := lambdaCode 0 (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1 d))
          (PolicyAssignment.assignmentCode p x.1.1 x.1.2).bind (fun h =>
            (PolicyAssignment.assignmentCode p x.1.1 u).bind (fun h' =>
              h.head?.bind (fun h₀ => some (finish (x.1,x.2,τ,u,h,h',h₀)))))))
      else none) :=
    (Computable.cond guard checked (Computable.const none)).of_eq (fun x => by
      by_cases h : 0 < SyntaxCode.typeLevel x.2 <;> simp [h])
  exact Computable.option_bind (Primrec.list_head?.to_comp.comp
    (Computable.fst : Computable (fun x : HeadInput => x.1))) body.to₂

private theorem selectedComputable (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) :
    Computable (compileSelected p) := by
  let Q := SelectedInput
  have hi : Computable (fun x : Q => x.1) := Computable.fst
  have hx : Computable (fun x : Q => x.2) := Computable.snd
  have tree := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.2
  have hm : Computable (fun y : Q × Code => moveCode y.1.1 y.2) :=
    movePrimitive.to_comp.comp (hi.comp Computable.fst) Computable.snd
  have tail : Computable (fun x : Code => compileHead p (x.1,CurrentTreeCode.expand x)) :=
    (headComputable p hp).comp (Computable.fst.pair CurrentTreeCode.effective.to_comp)
  have body : Computable (fun y : Q × Code =>
      (moveCode y.1.1 y.2).bind (fun a => compileHead p (a.1,CurrentTreeCode.expand a))) :=
    Computable.option_bind hm (tail.comp (Computable.snd :
      Computable (fun y : (Q × Code) × Code => y.2))).to₂
  exact Computable.option_bind (tree.comp (Computable.fst.comp hx) (Computable.snd.comp hx))
    body.to₂

theorem effective : CurrentOneUnitTargets.Effective :=
  ⟨equationPrimitive,fun p hp => ⟨headComputable p hp,selectedComputable p hp⟩⟩

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
