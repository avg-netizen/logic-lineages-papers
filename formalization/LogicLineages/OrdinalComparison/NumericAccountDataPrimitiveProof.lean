module
public import LogicLineages.OrdinalComparison.NumericAccountDataTargets
public import LogicLineages.OrdinalComparison.NumericCarrierDataPrimitiveProof
public import LogicLineages.OrdinalComparison.UnitHeadCodeProof
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericAccountData.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair
private abbrev D := List Nat×Nat
private abbrev S := List Nat×Nat

private theorem surplus_primitive : Primrec surplusCode := by
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hd := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hi := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hz := Primrec.eq.comp hi (Primrec.const 0)
  have hf : Primrec OrdinalSyntax.headLeafFree := Primrec.ite
    (Primrec.eq.comp hm (Primrec.const 3)) hz.not.decide (Primrec.const true)
  have hl : Primrec (fun n : Nat => (OrdinalSyntax.headLeafFree n, if OrdinalSyntax.headLeafFree n then 1 else 0)) :=
    hf.pair (Primrec.ite (Primrec.eq.comp hf (Primrec.const true)) (Primrec.const 1) (Primrec.const 0))
  have hb : Primrec (fun p : Nat×(Bool×Nat)×(Bool×Nat) =>
      (p.2.1.1 && p.2.2.1, if p.2.1.1 && p.2.2.1 then 1 else if p.1=4 then p.2.1.2+p.2.2.2+1 else 0)) := by
    have ha : Primrec (fun p : Nat×(Bool×Nat)×(Bool×Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hb : Primrec (fun p : Nat×(Bool×Nat)×(Bool×Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
    have hf := Primrec.and.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)
    exact hf.pair (Primrec.ite (Primrec.eq.comp hf (Primrec.const true)) (Primrec.const 1)
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4))
        (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp ha) (Primrec.snd.comp hb)) (Primrec.const 1))
        (Primrec.const 0)))
  exact Primrec.snd.comp (OrdinalSyntax.ordinalSyntaxFoldPrimitiveRecursive _ _ _ hl hb)

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

private abbrev CP := List Nat×Nat×Option D
private def collapseMap (q : CP×(Nat×Bool×Nat)) : Option D :=
  q.1.2.2.map (fun x => if q.2.2.1 then
    (x.1,x.2+q.2.2.2+surplusCode (SourceAnnotationCode.operatorHead q.1.2.1))
    else (x.1++[NumericCarrierData.carrierCode q.1.1 q.1.2.1],x.2+surplusCode (SourceAnnotationCode.operatorHead q.1.2.1)))
private theorem collapse_map_primitive : Primrec collapseMap := by
  let P := (CP×(Nat×Bool×Nat))×D
  have hop : Primrec (fun p : P => p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hctx : Primrec (fun p : P => p.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs := surplus_primitive.comp (head_primitive.comp hop)
  have hval : Primrec (fun p : P => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hbool : Primrec (fun p : P => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hout : Primrec (fun p : P => if p.1.2.2.1 then
      (p.2.1,p.2.2+p.1.2.2.2+surplusCode (SourceAnnotationCode.operatorHead p.1.1.2.1))
      else (p.2.1++[NumericCarrierData.carrierCode p.1.1.1 p.1.1.2.1],p.2.2+surplusCode (SourceAnnotationCode.operatorHead p.1.1.2.1))) :=
    Primrec.ite (Primrec.eq.comp hbool (Primrec.const true))
      (hx.pair (Primrec.nat_add.comp (Primrec.nat_add.comp hc hval) hs))
      ((Primrec.list_append.comp hx (Primrec.list_cons.comp
        (NumericCarrierData.Proof.primitiveRecursiveAlgorithms.2.2.2.2.comp hctx hop) (Primrec.const []))).pair
        (Primrec.nat_add.comp hc hs))
  exact Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) hout.to₂

private def collapseResult (p : CP) : Option D :=
  (UnitHeadCode.classify (SourceAnnotationCode.operatorHead p.2.1)).bind (fun v => collapseMap (p,v))
private theorem collapse_primitive : Primrec collapseResult :=
  Primrec.option_bind
    (UnitHeadCode.Proof.primitiveRecursiveAlgorithms.2.2.comp (head_primitive.comp (Primrec.fst.comp Primrec.snd)))
    collapse_map_primitive.to₂

private theorem account_primitive : Primrec₂ accountCode := by
  let children : S → List S := fun s =>
    if s.2%4=2 then [(s.1,(s.2/4).unpair.1),(s.1,(s.2/4).unpair.2)]
    else if s.2%4=3 then [(s.1,(s.2/4).unpair.2)] else []
  let base : S → Option D := fun s =>
    if OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2) then some ([],1)
    else if s.2%4=1 then some ([],1) else none
  let assemble : S → List (Option D) → Option (Option D) := fun s rs => some
    (if OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2) then base s
    else if s.2%4=2 then addResult (rs.getD 0 none) (rs.getD 1 none)
    else if s.2%4=3 then collapseResult (s.1,(s.2/4).unpair.1,rs.getD 0 none) else base s)
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
  have hasm : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : S×List (Option D) => p.2.getD k none) :=
      (Primrec.list_getD (none : Option D)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite (hf.comp Primrec.fst) (hb.comp Primrec.fst)
      (Primrec.ite ((ht 2).comp Primrec.fst) (add_primitive.comp (hg 0) (hg 1))
      (Primrec.ite ((ht 3).comp Primrec.fst)
        (collapse_primitive.comp ((Primrec.fst.comp Primrec.fst).pair ((hl.comp Primrec.fst).pair (hg 0))))
        (hb.comp Primrec.fst))))
  apply Primrec.nat_omega_rec' (fun s : S => accountCode s.1 s.2) Primrec.snd hc hasm
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
    conv_rhs => rw [accountCode]
    by_cases hf : OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 s.2)=true
    · simp [assemble,base,hf]
    · have ht : s.2%4=0 ∨ s.2%4=1 ∨ s.2%4=2 ∨ s.2%4=3 := by omega
      rcases ht with h|h|h|h <;>
        simp [assemble,children,base,addResult,collapseResult,collapseMap,hf,h]
      cases hv : UnitHeadCode.classify (SourceAnnotationCode.operatorHead (s.2/4).unpair.1) with
      | none => rfl
      | some val =>
        cases ht : accountCode s.1 (s.2/4).unpair.2 with
        | none => rfl
        | some t =>
          simp only [Option.bind_some,Option.map_some]
          cases hb : val.2.1 <;> simp [hb]

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  refine ⟨surplus_primitive,account_primitive,?_⟩
  have hb : Primrec (fun p : S => CanonicalAnnotationBuilderCode.buildCode p.1 0 p.2) :=
    CanonicalAnnotationBuilderCode.Proof.primitiveRecursive.comp
      (Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd))
  have ha : Primrec (fun q : S×(List Nat×Nat) => accountCode q.1.1 q.2.2) :=
    account_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have hout : Primrec (fun q : (S×(List Nat×Nat))×D => (q.1.2.1,q.2.1,q.2.2)) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  have h := Primrec.option_bind hb (Primrec.option_map ha hout.to₂).to₂
  apply h.of_eq
  intro p
  cases hbuild : CanonicalAnnotationBuilderCode.buildCode p.1 0 p.2 <;>
    simp [sourceAccountCode,hbuild]
  rename_i val
  cases accountCode p.1 val.2 <;> rfl
end LogicLineages.OrdinalComparison.Source.NumericAccountData.Proof
