module
public import LogicLineages.OrdinalComparison.DeterministicAccountDataTargets
public import LogicLineages.OrdinalComparison.DeterministicCarrierDataProof
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationProof
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderProof
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicAccountData.Proof
open ScalarAnnotationData ScalarCarrierAccounting ActiveScalarAnnotation

private theorem match_append {Γ} {rs ss : List (UnaryRecord Γ)} {xs ys : List Carrier}
    (h : List.Forall₂ Matches rs xs) (g : List.Forall₂ Matches ss ys) :
    List.Forall₂ Matches (rs ++ ss) (xs ++ ys) := by
  induction h with
  | nil => exact g
  | cons ha ht ih => exact .cons ha ih

private theorem inactive_case {k Γ} (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here)
    (hf : ordinalHeadFree (erase d) = true) :
    ∃ rs c labels, accountData d = some (rs,c) ∧
      List.Forall₂ Matches rs labels ∧ Account (erase d) labels c := by
  refine ⟨[],1,[],?_,.nil,.free (ScalarCarrierAccounting.Proof.inactive_of_headFree _ hf)⟩
  rw [accountData.eq_def,if_pos hf]

private theorem active_of_not_free {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hf : ordinalHeadFree q ≠ true) : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q := by
  classical
  by_contra hn
  exact hf (HeadFiniteSurplus.Proof.headFree_of_inactive q hn)

theorem exactDataAccounting : Targets.ExactDataAccounting := by
  intro k Γ d hd
  induction d with
  | free q => exact inactive_case _ (HeadFiniteSurplus.Proof.headFree_of_inactive q hd.2)
  | tracked =>
    refine ⟨[],1,[],?_,.nil,.tracked⟩
    rw [accountData.eq_def]
    simp [erase,ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs]
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (erase (.add a b)) = true
    · exact inactive_case _ hf
    obtain ⟨rs,c,xs,hr,hm,ha⟩ := iha hd.1
    obtain ⟨ss,e,ys,hs,hn,hb⟩ := ihb hd.2
    refine ⟨rs++ss,c+e+1,xs++ys,?_,match_append hm hn,.add (active_of_not_free _ hf) ha hb⟩
    rw [accountData.eq_def,if_neg hf]
    simp [hr,hs]
  | collapse op tail ih =>
    by_cases hf : ordinalHeadFree (erase (.collapse op tail)) = true
    · exact inactive_case _ hf
    obtain ⟨rs,c,xs,hr,hm,ht⟩ := ih hd.2.2.2
    obtain ⟨a,he,hev,hval,hfin,hnon,hcount,hunit⟩ :=
      UnitHeadEvaluation.Proof.actualOperatorClassification _ op hd.1
    by_cases hb : UnitHeadEvaluation.finiteCode (ForwardTranslation.closedPositiveCode a) = true
    · refine ⟨rs,c+UnitHeadEvaluation.finiteValueCode (ForwardTranslation.closedPositiveCode a)+HeadFiniteSurplus.surplus op.head,
        xs,?_,hm,.finite (active_of_not_free _ hf) (hcount hb).symm ht⟩
      rw [accountData.eq_def,if_neg hf]
      simp [he,hr,hb]
    · have hb' : UnitHeadEvaluation.finiteCode (ForwardTranslation.closedPositiveCode a) = false :=
        Bool.eq_false_iff.mpr hb
      have hc := DeterministicCarrierData.Proof.exactCarrierData k Γ op hd.1
      let recd := carrierRecord op
      have hassigned : recd.Assigned := hc.1
      have hground : recd.NoGround := hc.2.1
      let label := certify recd hassigned hground
      have hlabel : label.head = unitValue op.head := hc.2.2.1
      refine ⟨rs++[recd],c+HeadFiniteSurplus.surplus op.head,xs++[label],?_,
        match_append hm (.cons ⟨hassigned,hground,rfl⟩ .nil),
        .nonfinite label (active_of_not_free _ hf) (hnon.mp hb') hlabel ht⟩
      rw [accountData.eq_def,if_neg hf]
      simp [he,hr,hb,recd]

theorem exactRecordCertification : Targets.ExactRecordCertification := by
  intro Γ rs labels h
  induction h with
  | nil => exact ⟨rfl,rfl,by simp⟩
  | @cons r label rs labels hm ht ih =>
    obtain ⟨ha,hn,rfl⟩ := hm
    refine ⟨by simpa using congrArg Nat.succ ih.1,?_,?_⟩
    · simp only [List.map_cons]
      rw [ih.2.1]
      rfl
    · intro r' hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨ha,hn⟩
      · exact ih.2.2 r' hr

theorem actualSourceAccount : Targets.ActualSourceAccount := by
  intro k Γ n e
  obtain ⟨u,d,hb,hu,he,hd⟩ := SourceAnnotationBuilder.Proof.actualSourceData k _ .here n e
  obtain ⟨rs,c,labels,hr,hm,ha⟩ := exactDataAccounting k Γ d hd
  refine ⟨u,rs,c,labels,?_,hu,hm,?_⟩
  · simp [sourceAccount,hb,hr]
  · rw [← he]
    exact ha
end LogicLineages.OrdinalComparison.Source.DeterministicAccountData.Proof
