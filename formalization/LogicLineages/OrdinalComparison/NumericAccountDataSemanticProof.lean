module
public import LogicLineages.OrdinalComparison.NumericAccountDataTargets
public import LogicLineages.OrdinalComparison.NumericCarrierDataProof
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeProof
public import LogicLineages.OrdinalComparison.UnitHeadCodeProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericAccountData.Proof
open ScalarAnnotationData DeterministicAccountData

private theorem leaf_free (i j : Nat) : OrdinalSyntax.headLeafFree (8*Nat.pair i j+3) = decide (i≠0) := by
  have hm : (8*Nat.pair i j+3)%8=3 := by omega
  have hd : (8*Nat.pair i j+3)/8=Nat.pair i j := by omega
  simp [OrdinalSyntax.headLeafFree,hm,hd]

theorem exactScalarSurplus : Targets.ExactScalarSurplus := by
  intro Γ σ q
  unfold surplusData OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x <;> simp [OrdinalSyntax.termFold,OrdinalSyntax.componentCode,SourceTypedPorts.variableIndex,
      leaf_free,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs,HeadFiniteSurplus.surplus]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    simp only [OrdinalSyntax.termFold,iha,ihb]
    simp [HeadFiniteSurplus.surplus,ordinalHeadFree,ordinalHeadOccurs]
  | emul a b iha ihb =>
    simp only [OrdinalSyntax.termFold,iha,ihb]
    simp [HeadFiniteSurplus.surplus,ordinalHeadFree,ordinalHeadOccurs]
  | collapse a b iha ihb =>
    simp only [OrdinalSyntax.termFold,iha,ihb]
    simp [HeadFiniteSurplus.surplus,ordinalHeadFree,ordinalHeadOccurs]

private theorem surplus_correct {Γ σ} (q : OrdinalExpression (σ::Γ)) :
    surplusCode (OrdinalSyntax.typedCode q) = HeadFiniteSurplus.surplus q :=
  congrArg Prod.snd (exactScalarSurplus Γ σ q)

private theorem code_free {k Γ} (d : Tree k (Ty.curriedGround (k+1)::Γ) .here) :
    OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 (SourceAnnotationCode.code d)) =
      ordinalHeadFree (erase d) := by
  have he := SourceAnnotationCode.Proof.exactErasure k (Ty.curriedGround (k+1)::Γ) .here d
  change SourceAnnotationCode.eraseCode 0 (SourceAnnotationCode.code d) = _ at he
  rw [he,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect]

private theorem free_account {k Γ} (d : Tree k (Ty.curriedGround (k+1)::Γ) .here)
    (hf : ordinalHeadFree (erase d)=true) :
    accountCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode) (SourceAnnotationCode.code d) =
      (accountData d).map (fun p => (p.1.map recordCode,p.2)) := by
  rw [accountCode.eq_def]
  dsimp only
  rw [code_free,if_pos hf,accountData.eq_def,if_pos hf]
  rfl

theorem exactNumericAccounting : Targets.ExactNumericAccounting := by
  intro k Γ d
  induction d with
  | free q =>
    by_cases hf : ordinalHeadFree (erase (Tree.free (k := k) (F := .here) q))=true
    · exact free_account _ hf
    rw [accountCode.eq_def]
    dsimp only
    rw [code_free,if_neg hf,accountData.eq_def,if_neg hf]
    have hm : SourceAnnotationCode.code (Tree.free (k := k) (F := .here) q)%4=0 := by simp [SourceAnnotationCode.code]
    rw [if_pos hm]
    rfl
  | tracked =>
    rw [accountCode.eq_def]
    dsimp only
    rw [code_free,accountData.eq_def]
    simp [SourceAnnotationCode.code,erase,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs]
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (erase (.add a b))=true
    · exact free_account _ hf
    rw [accountCode.eq_def]
    dsimp only
    rw [code_free,if_neg hf,accountData.eq_def,if_neg hf]
    have hm : SourceAnnotationCode.code (.add a b)%4=2 := by simp [SourceAnnotationCode.code]
    have hd : SourceAnnotationCode.code (.add a b)/4=Nat.pair (SourceAnnotationCode.code a) (SourceAnnotationCode.code b) := by
      simp only [SourceAnnotationCode.code];omega
    simp only [hm,hd,Nat.unpair_pair,show ¬(2:Nat)=0 by decide,show ¬(2:Nat)=1 by decide,
      true_or,↓reduceIte,↓reduceDIte]
    rw [iha,ihb]
    cases ha : accountData a with
    | none => simp [ha,bind,pure]
    | some va =>
      rcases va with ⟨xs,c⟩
      cases hb : accountData b with
      | none => simp [ha,hb,bind,pure]
      | some vb =>
        rcases vb with ⟨ys,e⟩
        simp [ha,hb,bind,pure,List.map_append]
  | collapse op tail ih =>
    by_cases hf : ordinalHeadFree (erase (.collapse op tail))=true
    · exact free_account _ hf
    rw [accountCode.eq_def]
    dsimp only
    rw [code_free,if_neg hf,accountData.eq_def,if_neg hf]
    have hm : SourceAnnotationCode.code (.collapse op tail)%4=3 := by simp [SourceAnnotationCode.code]
    have hd : SourceAnnotationCode.code (.collapse op tail)/4=Nat.pair (SourceAnnotationCode.operatorCode op) (SourceAnnotationCode.code tail) := by
      simp only [SourceAnnotationCode.code];omega
    simp only [hm,hd,Nat.unpair_pair,show ¬(3:Nat)=0 by decide,show ¬(3:Nat)=1 by decide,
      show ¬(3:Nat)=2 by decide,or_true,↓reduceIte,↓reduceDIte]
    rw [(SourceAnnotationCode.Proof.exactOperatorCodec _ op).2.2.2,ih]
    rw [UnitHeadCode.classify,(UnitHeadCode.Proof.exactRawUnitExtraction _ op.head).2]
    rw [surplus_correct,NumericCarrierData.Proof.exactCarrierCode]
    cases he : UnitHeadEvaluation.extractUnitHead op.head with
    | none => simp [he,bind,pure]
    | some a =>
      cases ht : accountData tail with
      | none => simp [he,ht,bind,pure]
      | some p =>
        rcases p with ⟨xs,c⟩
        by_cases hfin : UnitHeadEvaluation.finiteCode (ForwardTranslation.closedPositiveCode a)=true
        · simp [he,ht,hfin,bind,pure]
        · simp [he,ht,hfin,bind,pure,List.map_append,recordCode,carrierRecord,
            SourceAnnotationCode.operatorCode,DeterministicCarrierData.carrierData]
          rfl
end LogicLineages.OrdinalComparison.Source.NumericAccountData.Proof
