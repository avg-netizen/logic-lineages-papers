module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof
open ActiveScalarAnnotation AdditiveHeadTree OriginalDomain HeadFiniteSurplus
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem accountingOrigin : Targets.AccountingOrigin := by
  intro k Γ q xs c hq
  induction hq with
  | free _ => simp
  | tracked => simp
  | add active left right ihl ihr =>
    intro label hl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨h,t,hs,hn,he⟩ := ihl label hl
      exact ⟨h,t,.addLeft hs,hn,he⟩
    · obtain ⟨h,t,hs,hn,he⟩ := ihr label hl
      exact ⟨h,t,.addRight hs,hn,he⟩
  | finite active finite tail ih =>
    intro label hl
    obtain ⟨h,t,hs,hn,he⟩ := ih label hl
    exact ⟨h,t,.tail hs,hn,he⟩
  | nonfinite label active nonfinite exactHead tail ih =>
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨h,t,hs,hn,he⟩ := ih c hc
      exact ⟨h,t,.tail hs,hn,he⟩
    · have he := List.mem_singleton.mp hc
      subst c
      exact ⟨_,_,.here active,nonfinite,exactHead⟩

private theorem inactive_account {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
    ∃ (xs : List Carrier) (c : Nat) (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
      Account q xs c ∧ AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v ∧
      ∀ μ : Variable Γ .ground → Nat,
        expressionValue (UnitObservation.substitution μ) (v (outputOne k)) = carrierSum xs + (c : Ordinal) := by
  refine ⟨[],1,ordinalFreePartialVector 0 q,.free hn,?_,?_⟩
  · rw [AdmissiblePartial.run.eq_def, if_pos (HeadFiniteSurplus.Proof.headFree_of_inactive q hn)]
  · intro μ
    simp [ordinalFreePartialVector, outputOne, expressionValue, denote, carrierSum]

private theorem head_partial_units {k Γ}
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) h) :
    ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
      AdmissiblePartial.run OrdinalSyntax.defaultPolicy 1 h = some v ∧
      ∀ μ : Variable Γ .ground → Nat,
        expressionValue (UnitObservation.substitution μ) (v (outputOne k)) =
          unitValue h + (surplus h : Ordinal) := by
  obtain ⟨_,v,hv,_,_,he⟩ := SelectedAffineHead.Proof.head_conclusion OrdinalSyntax.defaultPolicy h ht
  refine ⟨v,hv,?_⟩
  intro μ
  have hh := (he (fun _ => 0) μ).1
  have hu : expressionValue (UnitObservation.substitution (fun _ => 0)) h = unitValue h :=
    UnaryCarrier.Proof.positive_unit_value 1 h (by decide)
      (AdditiveHeadTree.Proof.head_grade ht) (fun _ => 0)
  exact hh.trans (congrArg (fun a => a + (surplus h : Ordinal)) hu)

theorem exactAccounting : Targets.ExactAccounting := by
  intro k Γ q hq
  induction hq with
  | @free q grade inactive =>
    intro _
    exact inactive_account q inactive
  | tracked =>
    intro _
    refine ⟨[],1,(fun _ => .one),.tracked,?_,?_⟩
    · rw [AdmissiblePartial.run.eq_def]
      simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
    · intro μ
      simp [expressionValue, denote, carrierSum]
  | @add a b ha hb iha ihb =>
    intro hannotation
    by_cases hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b)
    · exact inactive_account _ hn
    · have hactive : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b) := Classical.byContradiction hn
      have hfree : ordinalHeadFree (.add a b) ≠ true := by
        intro hf
        exact inactive_of_headFree _ hf hactive
      cases hannotation with
      | free hinactive => exact False.elim (hinactive hactive)
      | add hanna hannb =>
        obtain ⟨xs,c,va,haca,hva,hea⟩ := iha hanna
        obtain ⟨ys,d,vb,hacb,hvb,heb⟩ := ihb hannb
        refine ⟨xs++ys,c+d+1,(fun j => AdmissiblePartial.three OrdinalSyntax.defaultPolicy .activeAdd (va j) (vb j) .one),
          .add hactive haca hacb,?_,?_⟩
        · rw [AdmissiblePartial.run.eq_def, if_neg hfree]
          simp [hva,hvb]
        · intro μ
          change denote (valuation (UnitObservation.substitution μ)) _ = _
          rw [HeadFiniteSurplus.Proof.three_value]
          change ordinalNaturalSum (ordinalNaturalSum
            (expressionValue (UnitObservation.substitution μ) (va (outputOne k)))
            (expressionValue (UnitObservation.substitution μ) (vb (outputOne k)))) 1 = _
          rw [hea μ,heb μ,carrierSum_append]
          exact HeadFiniteSurplus.Proof.finite_surplus_add _ _ c d
  | @collapse h t hh ht ih =>
    intro hannotation
    by_cases hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t)
    · exact inactive_account _ hn
    · have hactive : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t) := Classical.byContradiction hn
      have hfree : ordinalHeadFree (.collapse h t) ≠ true := by
        intro hf
        exact inactive_of_headFree _ hf hactive
      cases hannotation with
      | free hinactive => exact False.elim (hinactive hactive)
      | collapse op support hant =>
        obtain ⟨xs,c,vt,hact,hvt,het⟩ := ih hant
        obtain ⟨vh,hvh,heh⟩ := head_partial_units h hh
        let v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)) := fun j =>
          if j.val = 0 then .collapse (ordinalHeadClosure h) (vt 0) else .add (vh j) (vt j)
        have hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (.collapse h t) = some v := by
          rw [AdmissiblePartial.run.eq_def, if_neg hfree]
          simp [hvh,hvt,v]
        have he : ∀ μ : Variable Γ .ground → Nat,
            expressionValue (UnitObservation.substitution μ) (v (outputOne k)) =
              ordinalNaturalSum (unitValue h + (surplus h : Ordinal)) (carrierSum xs + (c : Ordinal)) := by
          intro μ
          change ordinalNaturalSum (expressionValue (UnitObservation.substitution μ) (vh (outputOne k)))
            (expressionValue (UnitObservation.substitution μ) (vt (outputOne k))) = _
          rw [heh μ,het μ]
        by_cases hfinite : unitValue h < Ordinal.omega0
        · obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp hfinite
          refine ⟨xs,c+n+surplus h,v,.finite hactive hn hact,hv,?_⟩
          intro μ
          rw [he μ,hn]
          exact finite_account_step xs c n (surplus h)
        · have hnonfinite : Ordinal.omega0 ≤ unitValue h := le_of_not_gt hfinite
          obtain ⟨label,hlabel⟩ := carrier_for_operator h hh op
          refine ⟨xs++[label],c+surplus h,v,.nonfinite label hactive hnonfinite hlabel hact,hv,?_⟩
          intro μ
          rw [he μ,←hlabel]
          exact nonfinite_account_step xs label c (surplus h)

end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof
