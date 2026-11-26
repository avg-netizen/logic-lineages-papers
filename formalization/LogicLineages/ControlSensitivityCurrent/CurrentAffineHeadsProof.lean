module
public import LogicLineages.ControlSensitivityCurrent.CurrentAffineHeadsPositiveProof
public import LogicLineages.OrdinalComparison.SelectedAffineHeadProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus
open ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)

/-- Reuses the actual selected-p literal head calculation only after both
actual partial outputs and the original head have their own positive grades. -/
theorem actualHead : CurrentAffineHeadsTargets.ActualHead := by
  intro k Γ p f h ht
  obtain ⟨_,v,hr,hcount,hzero,hEval⟩ := SelectedAffineHead.Proof.head_conclusion p h ht
  have hg : GeneratedOrdinalGrade (Ty.curriedGround (k+1) :: Γ) 1 h :=
    AdditiveHeadTree.Proof.head_grade ht
  obtain ⟨w,hw,hgw⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ
    (Ty.curriedGround (k+1)) p 1 h hg
  have same : w = v := Option.some.inj (hw.symm.trans hr)
  subst w
  have hg₁ : GeneratedOrdinalGrade Γ 1 (v (outputOne k)) := hgw (outputOne k)
  have hg₂ : GeneratedOrdinalGrade Γ 2 (v (outputTwo k)) := hgw (outputTwo k)
  refine ⟨ht,hg,v,hr,hg₁,hg₂,hcount,hzero,?_⟩
  intro ρ μ
  have e₁ := (positiveNoCollapse Γ 1 (v (outputOne k)) (by decide) hg₁).2 f (commonUnits μ)
  have e₂ := (positiveNoCollapse Γ 2 (v (outputTwo k)) (by decide) hg₂).2 f (commonUnits μ)
  have eh := (positiveNoCollapse _ 1 h (by decide) hg).2 f (commonUnits ρ)
  rw [e₁,e₂,eh]
  have ho := hEval ρ μ
  simp only [OriginalDomain.expressionValue] at ho
  have hμ : OriginalDomain.valuation (UnitObservation.substitution μ) = commonUnits μ :=
    sameCommonUnits Γ μ
  have hρ : OriginalDomain.valuation (UnitObservation.substitution ρ) = commonUnits ρ :=
    sameCommonUnits (Ty.curriedGround (k+1) :: Γ) ρ
  rw [hμ,hρ] at ho
  exact ho

theorem completeSource : CurrentAffineHeadsTargets.CompleteSource := by
  intro k Γ n p f t hgen
  let Θ := Ty.curriedGround (k+1) :: Γ
  let F : Variable Θ (Ty.curriedGround (k+1)) := .here
  obtain ⟨e,he⟩ := (TrackedSource.Proof.exactGrammar k Θ F n t).mp hgen
  obtain ⟨u,hu,hs,hpos⟩ := AdditiveHeadTree.Proof.actualSourceTrees k Θ F n p e
  obtain ⟨a,ha,hann⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k Θ F n p e
  have same : a = u := Option.some.inj (ha.symm.trans hu)
  subst a
  rw [he] at hu
  refine ⟨u,hu,?_,?_⟩
  · intro j hj
    exact actualHead k Γ p f (u j) (hpos j hj)
  · intro h s hsel
    obtain ⟨hTree,hTail⟩ := SelectedAffineHead.Proof.selectedTreeSupport k Θ F p (u 0) h s hs hann hsel
    exact ⟨actualHead k Γ p f h hTree,hTail⟩

end LogicLineages.ControlSensitivityCurrent.CurrentAffineHeads
