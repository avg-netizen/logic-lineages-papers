module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveDeterminacyProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsStatementChecks
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus
open CurrentUnaryChain (commonUnits)
open AdmissibleSum ParametricSourceSuccessor

private theorem collapseValue (p : Policy) (f : Nat → Nat) {k Γ}
    (h t : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (hh : HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) h)
    (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h t))
    (xs : List (Carrier p)) (c : Nat)
    (vt : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (hvt : AdmissiblePartial.run p 0 t = some vt)
    (ht : ∀ μ : Variable Γ .ground → Nat,
      denoteWith f (commonUnits μ) (vt (outputOne k)) = carrierSum f xs + (c : Ordinal)) :
    ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
      AdmissiblePartial.run p 0 (.collapse h t) = some v ∧
      ∀ μ : Variable Γ .ground → Nat,
        denoteWith f (commonUnits μ) (v (outputOne k)) =
          ordinalNaturalSum (unitValue f h + (surplus h : Ordinal)) (carrierSum f xs + (c : Ordinal)) := by
  obtain ⟨_,_,vh,hvh,_,_,_,_,hhead⟩ :=
    CurrentAffineHeads.StatementChecks.actual_head_partial_finite_surplus k Γ p f h hh
  let v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)) := fun j =>
    if j.val = 0 then .collapse (ordinalHeadClosure h) (vt 0) else .add (vh j) (vt j)
  refine ⟨v,?_,?_⟩
  · rw [AdmissiblePartial.run.eq_def,if_neg (activeNotHeadFree ha)]
    simp [hvh,hvt,v]
  · intro μ
    change ordinalNaturalSum (denoteWith f (commonUnits μ) (vh (outputOne k)))
      (denoteWith f (commonUnits μ) (vt (outputOne k))) = _
    exact congrArg₂ ordinalNaturalSum (hhead (fun _ => 0) μ).1 (ht μ)

theorem exactAccountValue : CurrentReserveTargets.ExactAccountValue := by
  intro p f k Γ q xs c ht haccount
  revert ht
  induction haccount with
  | @free q hn =>
    intro _
    refine ⟨ordinalFreePartialVector 0 q,
      ?_,fun μ => ?_⟩
    · rw [AdmissiblePartial.run.eq_def,if_pos (HeadFiniteSurplus.Proof.headFree_of_inactive q hn)]
    · change (1 : Ordinal) = 0+(1 : Ordinal)
      simp
  | tracked =>
    intro _
    refine ⟨fun _ => .one,?_,fun μ => ?_⟩
    · rw [AdmissiblePartial.run.eq_def]
      simp [ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs]
    · change (1 : Ordinal) = 0+(1 : Ordinal)
      simp
  | @add a b xs ys c d ha _ _ iha ihb =>
    intro ht
    cases ht with
    | free _ hn => exact False.elim (hn ha)
    | add htA htB =>
      obtain ⟨vA,hvA,hA⟩ := iha htA
      obtain ⟨vB,hvB,hB⟩ := ihb htB
      refine ⟨fun j => AdmissiblePartial.three p .activeAdd (vA j) (vB j) .one,?_,?_⟩
      · rw [AdmissiblePartial.run.eq_def,if_neg (activeNotHeadFree ha)]
        simp [hvA,hvB]
      · intro μ
        rw [threeValue,hA μ,hB μ,carrierSumAppend]
        change ordinalNaturalSum (ordinalNaturalSum (carrierSum f xs + (c : Ordinal))
          (carrierSum f ys + (d : Ordinal))) 1 = _
        exact HeadFiniteSurplus.Proof.finite_surplus_add _ _ c d
  | @finite h t xs c n ha hf _ ih =>
    intro ht
    cases ht with
    | free _ hn => exact False.elim (hn ha)
    | collapse hH hT =>
      obtain ⟨vt,hvt,hT'⟩ := ih hT
      obtain ⟨v,hv,hV⟩ := collapseValue p f h t hH ha xs c vt hvt hT'
      refine ⟨v,hv,?_⟩
      intro μ
      rw [hV μ,hf]
      exact finiteAccountStep f xs c n (surplus h)
  | @nonfinite h t xs c a ha hnf he _ _ ih =>
    intro ht
    cases ht with
    | free _ hn => exact False.elim (hn ha)
    | collapse hH hT =>
      obtain ⟨vt,hvt,hT'⟩ := ih hT
      obtain ⟨v,hv,hV⟩ := collapseValue p f h t hH ha xs c vt hvt hT'
      refine ⟨v,hv,?_⟩
      intro μ
      rw [hV μ,← he]
      exact nonfiniteAccountStep f xs a c (surplus h)

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
