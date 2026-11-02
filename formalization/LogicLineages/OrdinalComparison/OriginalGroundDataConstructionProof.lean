module
public import LogicLineages.OrdinalComparison.OriginalGroundDataConstructionTargets
public import LogicLineages.OrdinalComparison.DeterministicAccountDataProof
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListProof
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetProof
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundDataConstruction.Proof
open DeterministicAccountData ScalarCarrierAccounting OriginalDomain OriginalScaleFlatList
open AdmissibleAssignment

theorem exactPackaging : Targets.ExactPackaging := by
  intro k Γ rs ha
  constructor
  · simp [operators]
  · simp [operators,List.map_map]

theorem actualPaidAccount : Targets.ActualPaidAccount := by
  intro k Γ P hactive
  obtain ⟨u,rs,c,labels,hr,hu,hm,hac⟩ := DeterministicAccountData.Proof.actualSourceAccount k Γ 0 P
  obtain ⟨u',hu',hex,hbound⟩ := SourceReserveLowerBound.Proof.actualSourceLowerBound k Γ 0 P
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hh := (SourceReserveLowerBound.Proof.ground_floor P hactive).trans (hbound labels c hac)
  have hlen := (DeterministicAccountData.Proof.exactRecordCertification _ rs labels hm).1
  unfold reserve at hh
  refine ⟨u,rs,c,labels,hr,hu,hm,hac,?_⟩
  omega

theorem abstraction_first (k : Nat) (Γ : List Ty)
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v)
    (hB : abstraction OrdinalSyntax.defaultPolicy u = some B) :
    B (boxFirst k) = v (HeadFiniteSurplus.outputOne k) := by
  have hu : u = (fun _ : Fin 1 => u 0) := by funext j;rw [Fin.eq_zero j]
  rw [hu] at hB
  unfold abstraction at hB
  simp only [collect,Fin.val_zero,hv,Option.bind_some] at hB
  have he := congrArg (fun w : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level =>
    w (boxFirst k)) (Option.some.inj hB)
  simp [boxFirst,HeadFiniteSurplus.outputOne,OriginalSecondBudget.Proof.functional_level_one,
    OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,
    AdmissibleSum.expand,Fin.cases_zero,Ty.level] at he
  exact he.symm

theorem packaged_sum {k Γ}
    (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
    (ha : ∀ r ∈ rs,r.Assigned) (labels : List Carrier)
    (hm : List.Forall₂ Matches rs labels) : sourceSum (operators rs ha) = carrierSum labels := by
  have he := (exactPackaging k Γ rs ha).2
  have ht := (DeterministicAccountData.Proof.exactRecordCertification _ rs labels hm).2.1
  rw [sourceSum,he,ht,AccountSemanticDeterminacy.Proof.carrierSum_trace]
  rfl

theorem actualOriginalGroundConstruction : Targets.ActualOriginalGroundConstruction := by
  intro k Γ P C hactive
  obtain ⟨u,rs,c,labels,hr,hu,hm,hac,hpaid⟩ := actualPaidAccount k Γ P hactive
  have hcert := DeterministicAccountData.Proof.exactRecordCertification _ rs labels hm
  let hraw : ∀ r ∈ rs,r.Assigned := fun r h => (hcert.2.2 r h).1
  obtain ⟨u',B,caller,b,hu',hB,hcaller,hb,hfour,hbox,hbval⟩ :=
    OriginalSecondBudget.Proof.originalFullBoxBudget k Γ P C hactive
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨u',v,hu',hv,hex,hsound⟩ := AccountSemanticDeterminacy.Proof.actualSourceSoundness k Γ 0 P
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hab := hB
  change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P)).bind
    (fun w => abstraction OrdinalSyntax.defaultPolicy w) = some B at hab
  rw [hu] at hab
  have hfirst := abstraction_first k Γ u v B hv hab
  have hBval : ∀ ρ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution ρ) (B (boxFirst k)) =
        sourceSum (operators rs hraw) + (c : Ordinal) := by
    intro ρ
    rw [hfirst,packaged_sum rs hraw labels hm]
    exact hsound labels c hac ρ
  have hp : 3*(operators rs hraw).length+4 ≤ c := by
    rw [(exactPackaging k Γ rs hraw).1]
    exact hpaid
  obtain ⟨caller',vC,hcaller',hSat,hCvalue,K,hK,hgap,hbalance⟩ :=
    OriginalScaleFlatList.Proof.actualOriginalScaleChain k Γ (operators rs hraw) C b c hfour hp
  have he : caller' = caller := Option.some.inj (hcaller'.symm.trans hcaller)
  subst caller'
  refine ⟨u,B,caller,b,rs,c,hraw,hr,hu,hB,hcaller,hb,hfour,hpaid,hbox,hbval,
    vC,hSat,hCvalue,K,hK,hgap,?_⟩
  intro ρ μ
  rw [hBval ρ]
  exact hbalance ρ μ
end LogicLineages.OrdinalComparison.Source.OriginalGroundDataConstruction.Proof
