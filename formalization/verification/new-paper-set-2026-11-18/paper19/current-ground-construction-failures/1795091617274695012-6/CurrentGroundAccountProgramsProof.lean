module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountCarrierProgramsProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationBuildProgramsProof
public import LogicLineages.OrdinalComparison.NumericAccountDataPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountPrograms

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum
open CurrentGroundAnnotationPrograms (chooseProgram)
attribute [local irreducible] Nat.sqrt Nat.unpair
private abbrev R := NumericUnaryChain.RawOperator
private abbrev D := List R × Nat
private abbrev S := List Nat × Nat
private abbrev C := Nat × Bool × Nat
private abbrev CP := List Nat × Nat × Option D
private abbrev P := (CP × C) × D

private def addResult (a b : Option D) : Option D := do
  let x ← a
  let y ← b
  pure (x.1++y.1,x.2+y.2+1)
private theorem add_primitive : Primrec₂ addResult := by
  have hv : Primrec (fun p : D×D => (p.1.1++p.2.1,p.1.2+p.2.2+1)) :=
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)) (Primrec.const 1))
  have h : Primrec (fun p : Option D×Option D =>
      p.1.bind (fun x => p.2.map (fun y => (x.1++y.1,x.2+y.2+1)))) :=
    Primrec.option_bind Primrec.fst
      (Primrec.option_map (Primrec.snd.comp Primrec.fst)
        (hv.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂
  exact h.of_eq (fun p => by cases p.1 <;> cases p.2 <;> rfl)

private theorem head_primitive : Primrec SourceAnnotationCode.operatorHead := by
  have hv : Primrec SourceAnnotationCode.operatorVector := Primrec.option_getD.comp
    (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))) (Primrec.const [])
  exact (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)


private def collapseMap (pol : Policy) (q : CP × C) : Option D := do
  let x ← q.1.2.2
  if q.2.2.1 then
    pure (x.1,x.2+q.2.2.2+NumericAccountData.surplusCode (SourceAnnotationCode.operatorHead q.1.2.1))
  else
    let r ← CurrentGroundAccount.carrierCode pol q.1.1 q.1.2.1
    pure (x.1++[r],x.2+NumericAccountData.surplusCode (SourceAnnotationCode.operatorHead q.1.2.1))

private theorem collapseMapProgram (pol : Policy) (hpol : PolicyShape.Effective pol) :
    Computable (collapseMap pol) := by
  have hop : Primrec (fun p : P => p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hctx : Primrec (fun p : P => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs := NumericAccountData.Proof.primitiveRecursiveAlgorithms.1.comp (head_primitive.comp hop)
  have hval : Primrec (fun p : P => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hbool : Primrec (fun p : P => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hfin : Primrec (fun q : P => some (q.2.1,q.2.2+q.1.2.2.2+
      NumericAccountData.surplusCode (SourceAnnotationCode.operatorHead q.1.1.2.1))) :=
    Primrec.option_some.comp (hx.pair (Primrec.nat_add.comp (Primrec.nat_add.comp hc hval) hs))
  have hcr := (carrierProgram pol hpol).comp (hctx.pair hop).to_comp
  have hout : Primrec (fun z : P × R =>
      (z.1.2.1++[z.2],z.1.2.2+NumericAccountData.surplusCode (SourceAnnotationCode.operatorHead z.1.1.1.2.1))) :=
    (Primrec.list_append.comp (hx.comp Primrec.fst)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))).pair
      ((Primrec.nat_add.comp hc hs).comp Primrec.fst)
  have hnon := Computable.option_map hcr hout.to_comp.to₂
  have hg : Computable (fun q : CP × C => q.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have h := Computable.option_bind hg
    (chooseProgram (Primrec.eq.comp hbool (Primrec.const true)) hfin.to_comp hnon).to₂
  apply h.of_eq
  intro q
  simp [collapseMap,Option.map_eq_bind]

private def collapseResult (p : Policy) (q : CP) : Option D :=
  (UnitHeadCode.classify (SourceAnnotationCode.operatorHead q.2.1)).bind (fun v => collapseMap p (q,v))

private theorem collapseProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (collapseResult p) :=
  Computable.option_bind
    (UnitHeadCode.Proof.primitiveRecursiveAlgorithms.2.2.comp
      (head_primitive.comp (Primrec.fst.comp Primrec.snd))).to_comp (collapseMapProgram p hp).to₂

theorem accountProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun z : List Nat × Nat => CurrentGroundAccount.accountCode p z.1 z.2) := by
  let children : S → List S := fun s =>
    if s.2%4=2 then [(s.1,(s.2/4).unpair.1),(s.1,(s.2/4).unpair.2)]
    else if s.2%4=3 then [(s.1,(s.2/4).unpair.2)] else []
  let base : S → Option D := fun s =>
    if OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2) then some ([],1)
    else if s.2%4=1 then some ([],1) else none
  let assemble : S → List (Option D) → Option (Option D) := fun s rs => some
    (if OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2) then base s
    else if s.2%4=2 then addResult (rs.getD 0 none) (rs.getD 1 none)
    else if s.2%4=3 then collapseResult p (s.1,(s.2/4).unpair.1,rs.getD 0 none) else base s)
  have htag : Primrec (fun s : S => s.2%4) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hpay : Primrec (fun s : S => s.2/4) := Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : S => s.2%4=k) := Primrec.eq.comp htag (Primrec.const k)
  have hfree : Primrec (fun s : S => OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2)) :=
    OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp
      (SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.1.comp (Primrec.const 0) Primrec.snd)
  have hf : PrimrecPred (fun s : S => OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2)=true) :=
    Primrec.eq.comp hfree (Primrec.const true)
  have hc : Primrec children := Primrec.ite (ht 2)
    (Primrec.list_cons.comp (Primrec.fst.pair hl) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 3) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])) (Primrec.const []))
  have hb : Primrec base := Primrec.ite hf (Primrec.const (some ([],1)))
    (Primrec.ite (ht 1) (Primrec.const (some ([],1))) (Primrec.const none))
  have hasm : Computable (fun z : S × List (Option D) => assemble z.1 z.2) := by
    have hg (k : Nat) : Primrec (fun p : S×List (Option D) => p.2.getD k none) :=
      (Primrec.list_getD (none : Option D)).comp Primrec.snd (Primrec.const k)
    exact Computable.option_some.comp (chooseProgram (hf.comp Primrec.fst) (hb.comp Primrec.fst).to_comp
      (chooseProgram ((ht 2).comp Primrec.fst) (add_primitive.comp (hg 0) (hg 1)).to_comp
      (chooseProgram ((ht 3).comp Primrec.fst)
        ((collapseProgram p hp).comp (((Primrec.fst.comp Primrec.fst).pair ((hl.comp Primrec.fst).pair (hg 0))).to_comp))
        (hb.comp Primrec.fst).to_comp)))
  apply ComputableRankedProof.ranked S (Option D)
    (fun s => CurrentGroundAccount.accountCode p s.1 s.2) (fun s => s.2) children assemble Primrec.snd hc hasm
  · intro s t hm
    change t.2<s.2
    by_cases h2 : s.2%4=2
    · have hd : s.2/4<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h2,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h3 : s.2%4=3
      · have hd : s.2/4<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h2,if_pos h3,List.mem_singleton] at hm
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h2,h3] at hm
  · intro s
    conv_rhs => rw [CurrentGroundAccount.accountCode]
    by_cases hf : OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2)=true
    · simp [assemble,base,hf]
    · have ht : s.2%4=0 ∨ s.2%4=1 ∨ s.2%4=2 ∨ s.2%4=3 := by omega
      rcases ht with h|h|h|h <;>
        simp [assemble,children,base,addResult,collapseResult,collapseMap,hf,h]
      cases hv : UnitHeadCode.classify (SourceAnnotationCode.operatorHead (s.2/4).unpair.1) with
      | none => rfl
      | some val =>
        cases ht : CurrentGroundAccount.accountCode p s.1 (s.2/4).unpair.2 with
        | none => rfl
        | some t =>
          rcases val with ⟨normal,finite,n⟩
          rcases t with ⟨xs,c⟩
          cases finite <;> rfl


theorem sourceProgram (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun z : List Nat × Nat => CurrentGroundAccount.sourceCode p z.1 z.2) := by
  have hb : Computable (fun q : S => CurrentGroundAnnotationCode.buildCode p q.1 0 q.2) :=
    (CurrentGroundAnnotationPrograms.buildProgram p hp).comp
      (Computable.fst.pair ((Computable.const 0).pair Computable.snd))
  have ha : Computable (fun q : S × (List Nat × Nat) => CurrentGroundAccount.accountCode p q.1.1 q.2.2) :=
    (accountProgram p hp).comp ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd))
  have hout : Primrec (fun q : (S × (List Nat × Nat)) × D => (q.1.2.1,q.2.1,q.2.2)) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  have h := Computable.option_bind hb (Computable.option_map ha hout.to_comp.to₂).to₂
  apply h.of_eq
  intro q
  simp [CurrentGroundAccount.sourceCode,Option.map_eq_bind]

theorem algorithmsEffective : CurrentGroundAccountTargets.AlgorithmsEffective := by
  intro p hp
  exact ⟨carrierProgram p hp,accountProgram p hp,sourceProgram p hp⟩

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountPrograms
