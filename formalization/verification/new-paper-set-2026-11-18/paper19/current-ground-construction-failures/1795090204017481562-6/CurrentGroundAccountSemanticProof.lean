module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountCarrierProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationBuildProof
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveSourceFloorProof
public import LogicLineages.OrdinalComparison.NumericAccountDataSemanticProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAccount

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum ScalarAnnotationData AdditiveHeadTree ActiveScalarAnnotation
open DeterministicAccountData (UnaryRecord)
open CurrentReserve (Carrier Account SpawnedAccount forgetOrigins unitValue)

private theorem codeFree {k Γ} (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here) :
    OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 (SourceAnnotationCode.code d)) =
      ordinalHeadFree (erase d) := by
  have he := SourceAnnotationCode.Proof.exactErasure k (Ty.curriedGround (k+1) :: Γ) .here d
  change SourceAnnotationCode.eraseCode 0 (SourceAnnotationCode.code d) = _ at he
  rw [he,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect]

private theorem freeAccount (p : Policy) (f : Nat → Nat) {k Γ}
    (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here)
    (hf : ordinalHeadFree (erase d) = true) :
    accountData p d = some ([],1) ∧
    SpawnedAccount p f (erase d) [] 1 ∧
    accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
      (SourceAnnotationCode.code d) = some ([],1) := by
  refine ⟨?_,.free (CurrentReserve.inactiveOfHeadFree _ hf),?_⟩
  · rw [accountData.eq_def,if_pos hf]
  · rw [accountCode.eq_def]
    dsimp only
    rw [codeFree,if_pos hf]

private theorem noFreeActive {k Γ} (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (h : ¬ ordinalHeadFree q = true) : Active (.here : Variable _ _) q := by
  classical
  by_contra hn
  exact h (HeadFiniteSurplus.Proof.headFree_of_inactive q hn)

private theorem freeCaseResult (p : Policy) (f : Nat → Nat) {k Γ}
    (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here)
    (hf : ordinalHeadFree (erase d) = true) :
    ∃ (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
      (xs : List (Carrier p)) (c : Nat),
      accountData p d = some (rs,c) ∧ List.Forall₂ Matches rs xs ∧
      SpawnedAccount p f (erase d) xs c ∧ Account p f (erase d) xs c ∧
      accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        (SourceAnnotationCode.code d) = some (rs.map recordCode,c) := by
  obtain ⟨hd,ha,hc⟩ := freeAccount p f d hf
  exact ⟨[],[],1,hd,.nil,ha,forgetOrigins ha,hc⟩

private theorem surplusCorrect {Γ σ} (q : OrdinalExpression (σ :: Γ)) :
    NumericAccountData.surplusCode (OrdinalSyntax.typedCode q) = HeadFiniteSurplus.surplus q :=
  congrArg Prod.snd (NumericAccountData.Proof.exactScalarSurplus Γ σ q)

theorem actualAccount : CurrentGroundAccountTargets.ActualAccount := by
  intro p f k Γ d
  induction d with
  | free q =>
    intro hd
    exact freeCaseResult p f _ (HeadFiniteSurplus.Proof.headFree_of_inactive q hd.2)
  | tracked =>
    intro _
    let q : Tree k (Ty.curriedGround (k+1) :: Γ) .here := .tracked
    have hf : ordinalHeadFree (erase q) = false := rfl
    refine ⟨[],[],1,?_,.nil,.tracked,.tracked,?_⟩
    · change accountData p q = some ([],1)
      rw [accountData.eq_def]
      simp [hf,q]
    · change accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        (SourceAnnotationCode.code q) = some ([],1)
      rw [accountCode.eq_def]
      dsimp only
      rw [codeFree]
      simp [hf,q,SourceAnnotationCode.code]
  | add a b iha ihb =>
    intro hd
    let d := Tree.add a b
    by_cases hf : ordinalHeadFree (erase d) = true
    · exact freeCaseResult p f d hf
    obtain ⟨rs,xs,c,ha,hm,hax,_,hca⟩ := iha hd.1
    obtain ⟨ss,ys,e,hb,hn,hby,_,hcb⟩ := ihb hd.2
    have world : SpawnedAccount p f (erase d) (xs++ys) (c+e+1) :=
      .add (noFreeActive (erase d) hf) hax hby
    refine ⟨rs++ss,xs++ys,c+e+1,?_,hm.append hn,world,forgetOrigins world,?_⟩
    · change accountData p d = _
      rw [accountData.eq_def,if_neg hf]
      simp [d,ha,hb,bind,pure]
    · change accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        (SourceAnnotationCode.code d) = _
      have hm : SourceAnnotationCode.code d % 4 = 2 := by simp [d,SourceAnnotationCode.code]
      have hdiv : SourceAnnotationCode.code d / 4 =
          Nat.pair (SourceAnnotationCode.code a) (SourceAnnotationCode.code b) := by
        simp only [d,SourceAnnotationCode.code]; omega
      rw [accountCode.eq_def]
      dsimp only
      rw [codeFree,if_neg hf]
      simp only [hm,hdiv,Nat.unpair_pair,show ¬(2:Nat)=0 by decide,show ¬(2:Nat)=1 by decide,
        true_or,↓reduceIte,↓reduceDIte]
      simp [hca,hcb,List.map_append,bind,pure]
  | collapse op tail ih =>
    intro hd
    let d := Tree.collapse op tail
    by_cases hf : ordinalHeadFree (erase d) = true
    · exact freeCaseResult p f d hf
    obtain ⟨rs,xs,c,hta,hm,hx,_,hr⟩ := ih hd.2.2.2
    have hgrade := AdditiveHeadTree.Proof.head_grade hd.2.1
    obtain ⟨normal,finite,value,hclass,_,hnf,hval⟩ :=
      currentHeadClassification f (Ty.curriedGround (k+1) :: Γ) 1 op.head hgrade (by decide)
    have hcodec := (SourceAnnotationCode.Proof.exactOperatorCodec _ op).2.2.2
    have hmod : SourceAnnotationCode.code d % 4 = 3 := by simp [d,SourceAnnotationCode.code]
    have hdiv : SourceAnnotationCode.code d / 4 =
        Nat.pair (SourceAnnotationCode.operatorCode op) (SourceAnnotationCode.code tail) := by
      simp only [d,SourceAnnotationCode.code]; omega
    cases hfin : finite with
    | true =>
      let sum := c+value+HeadFiniteSurplus.surplus op.head
      have label : SpawnedAccount p f (erase d) xs sum :=
        .finite (noFreeActive (erase d) hf) (hval hfin).symm hx
      refine ⟨rs,xs,sum,?_,hm,label,forgetOrigins label,?_⟩
      · change accountData p d = _
        rw [accountData.eq_def,if_neg hf]
        simp [d,hclass,hfin,hta,sum,bind,pure]
      · change accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
          (SourceAnnotationCode.code d) = _
        rw [accountCode.eq_def]
        dsimp only
        rw [codeFree,if_neg hf]
        simp only [hmod,hdiv,Nat.unpair_pair,show ¬(3:Nat)=0 by decide, show ¬(3:Nat)=1 by decide,
          show ¬(3:Nat)=2 by decide,or_true,↓reduceIte,↓reduceDIte]
        simp [hcodec,hclass,hfin,hr,surplusCorrect,sum,bind,pure]
    | false =>
      let sum := c+HeadFiniteSurplus.surplus op.head
      obtain ⟨r,w,hRec,_,⟨hReal,hmr⟩,hrc⟩ := literalCarrier p f k Γ op hd.1
      let a := CurrentReserve.carrierFrom hReal
      have hv := hReal.2.2.2.2.2.2.2 (fun _ => 0) (fun _ => 0)
      have he : a.head f = unitValue f op.head := hv
      have ho : CurrentReserve.LiteralOrigin p f op.head a :=
        ⟨op.arity,op.source,op.vector,w,r.vector,rfl,hReal,rfl⟩
      have label : SpawnedAccount p f (erase d) (xs++[a]) sum :=
        .nonfinite a (noFreeActive (erase d) hf) (hnf.1 hfin) he (fun _ => ho) hx
      refine ⟨rs++[r],xs++[a],sum,?_,hm.append (.cons hmr .nil),label,forgetOrigins label,?_⟩
      · change accountData p d = _
        rw [accountData.eq_def,if_neg hf]
        simp [d,hclass,hfin,hta,hRec,sum,bind,pure]
      · change accountCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
          (SourceAnnotationCode.code d) = _
        rw [accountCode.eq_def]
        dsimp only
        rw [codeFree,if_neg hf]
        simp only [hmod,hdiv,Nat.unpair_pair,show ¬(3:Nat)=0 by decide, show ¬(3:Nat)=1 by decide,
          show ¬(3:Nat)=2 by decide,or_true,↓reduceIte,↓reduceDIte]
        simp [hcodec,hclass,hfin,hr,hrc,surplusCorrect,sum,List.map_append,bind,pure]

private theorem renameIdentity {Γ} (q : OrdinalExpression Γ) :
    ordinalExpressionRename (fun x => x) q = q := by
  induction q with
  | var c => rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [ordinalExpressionRename,substitute] at iha ihb ⊢
    rw [iha,ihb]

theorem sourceAccount : CurrentGroundAccountTargets.SourceAccount := by
  intro p f k Γ n P
  obtain ⟨u,d,hbuild,hu,hv,he,hcode⟩ := CurrentGroundAnnotation.actualAnnotation p k
    (Ty.curriedGround (k+1) :: Γ) .here n P
  obtain ⟨rs,xs,c,hd,hm,hSpawn,hAcc,hRaw⟩ := actualAccount p f k Γ d hv
  have hs := (CurrentGroundAnnotation.validTree p k (Ty.curriedGround (k+1) :: Γ) .here d hv).1
  rw [he] at hSpawn hAcc hs
  obtain ⟨v,hv,hval⟩ := CurrentReserve.exactAccountValue p f k Γ (u 0) xs c hs hAcc
  have floor := CurrentReserve.renamedSourceFloor p f k (Ty.curriedGround (k+1) :: Γ) Γ .here n P u
    (fun x => x) (fun _ => Function.injective_id) rfl hu xs c
  rw [renameIdentity] at floor
  refine ⟨u,rs,xs,c,v,?_,?_,hu,hm,hSpawn,hAcc,floor hAcc,hv,hval⟩
  · simp [sourceData,hbuild,hd,bind,pure]
  · have hcode' : CurrentGroundAnnotationCode.buildCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
        0 (SyntaxCode.encodeTerm (TrackedSource.erase P)) =
      some (OrdinalSyntax.vectorCode u,SourceAnnotationCode.code d) := hcode
    simp [sourceCode,hcode',hRaw,bind,pure]

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAccount
