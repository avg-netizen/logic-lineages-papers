module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveAlgebraProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsPositiveProof
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetCountProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget

open LogicLineages.OrdinalComparison (ordinalNaturalSum)
open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open AdmissibleSum HeadFiniteSurplus OriginalSecondBudget AdditiveHeadTree
open ParametricSourceSuccessor

private theorem freeSecond (p : Policy) {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (hf : ordinalHeadFree q = true) (hv : AdmissiblePartial.run p 0 q = some v)
    (f : Nat → Nat) (ν : OrdinalComponent Γ → Ordinal) :
    denoteWith f ν (v (outputTwo k)) = (scalarSecond q : Ordinal) := by
  rw [AdmissiblePartial.run.eq_def,if_pos hf] at hv
  cases hv
  rw [OriginalSecondBudget.Proof.scalarSecond_of_free q hf]
  simp [ordinalFreePartialVector,outputTwo,denoteWith]

theorem scalarCountOfRun (p : Policy) {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : ScalarTrees (.here : Variable (Ty.curriedGround (k+1)::Γ) _) q)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (hv : AdmissiblePartial.run p 0 q = some v)
    (f : Nat → Nat) (ν : OrdinalComponent Γ → Ordinal) :
    denoteWith f ν (v (outputTwo k)) = (scalarSecond q : Ordinal) := by
  induction ht generalizing v with
  | @free q hg hn =>
    exact freeSecond p q v (HeadFiniteSurplus.Proof.headFree_of_inactive q hn) hv f ν
  | tracked =>
    rw [AdmissiblePartial.run.eq_def] at hv
    simp [ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs] at hv
    subst v
    simp [denoteWith,scalarSecond]
  | @add a b ha hb iha ihb =>
    by_cases hf : ordinalHeadFree (.add a b) = true
    · exact freeSecond p _ v hf hv f ν
    · rw [AdmissiblePartial.run.eq_def,if_neg hf] at hv
      dsimp only at hv
      cases hva : AdmissiblePartial.run p 0 a with
      | none => simp [hva] at hv
      | some va =>
        cases hvb : AdmissiblePartial.run p 0 b with
        | none => simp [hva,hvb] at hv
        | some vb =>
          simp [hva,hvb] at hv
          subst v
          rw [CurrentReserve.threeValue p f .activeAdd ν, iha va hva, ihb vb hvb]
          simpa [denoteWith,scalarSecond,hf] using HeadFiniteSurplus.Proof.finite_count_add
            (scalarSecond a) (scalarSecond b)
  | @collapse h t hh ht ih =>
    by_cases hf : ordinalHeadFree (.collapse h t) = true
    · exact freeSecond p _ v hf hv f ν
    · obtain ⟨vh,hvh,eh⟩ := HeadFiniteSurplus.Proof.exactHeadPartial k Γ p h hh
      obtain ⟨w,hw,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
        (Ty.curriedGround (k+1)) p 1 h (AdditiveHeadTree.Proof.head_grade hh)
      have hw' : w = vh := Option.some.inj (hw.symm.trans hvh)
      subst w
      have hval := (CurrentAffineHeads.positiveNoCollapse Γ 2 (vh (outputTwo k))
        (by decide) (hg (outputTwo k))).2 f ν
      rw [AdmissiblePartial.run.eq_def,if_neg hf] at hv
      dsimp only at hv
      cases hvt : AdmissiblePartial.run p 0 t with
      | none => simp [hvh,hvt] at hv
      | some vt =>
        simp [hvh,hvt] at hv
        subst v
        change ordinalNaturalSum (denoteWith f ν (vh (outputTwo k)))
          (denoteWith f ν (vt (outputTwo k))) = _
        rw [hval,(eh ν).2,ih vt hvt]
        simpa [scalarSecond,hf] using naturalSum_finite (secondCount h) (scalarSecond t)

theorem exactScalarSecond : CurrentGroundBudgetTargets.ExactScalarSecond := by
  intro p k Γ q ht
  obtain ⟨v,hv,_⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
    (Ty.curriedGround (k+1)) p 0 q (AdditiveHeadTree.Proof.scalar_grade ht)
  exact ⟨v,hv,OriginalSecondBudget.Proof.scalarSecond_pos q,scalarCountOfRun p q ht v hv⟩

end LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget
