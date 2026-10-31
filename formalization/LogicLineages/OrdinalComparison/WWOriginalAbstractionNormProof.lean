module
public import LogicLineages.OrdinalComparison.WWOriginalAbstractionNormTargets
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment

theorem originalHeadClosureVectorBounded : Targets.OriginalHeadClosureVectorBounded := by
  intro Γ σ m h hb ρ j
  obtain ⟨ρ', hh, ho⟩ := originalHeadOneExtension Γ σ ρ
  have hn := hb ρ' j
  rwa [← originalHeadClosureValue Γ σ ρ ρ' hh ho (h j),
    ← originalHeadClosureValue Γ σ ρ ρ' hh ho (h 0)] at hn

private theorem add_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) (f g : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ρ (.add f g)) =
      actualOrdinalNorm (expressionValue ρ f) + actualOrdinalNorm (expressionValue ρ g) :=
  actualNaturalSumNormAdditivity _ _ (originalExpressionValueBelowEpsilonZero Γ ρ f)
    (originalExpressionValueBelowEpsilonZero Γ ρ g)

theorem originalSourceAbstractionBounded : Targets.OriginalSourceAbstractionBounded := by
  intro Γ σ m p h hg hb
  obtain ⟨d, hd, gd, bd⟩ := originalDeltaPreservesBoundedNorm Γ σ m p h hg hb
  have bh := originalHeadClosureVectorBounded Γ σ m h
    ((originalBoundedVectorSupportBridge (σ :: Γ) m h).mpr hb)
  have bd' := (originalBoundedVectorSupportBridge Γ _ d).mpr bd
  let v : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
    if hm : j.val < m + 1 then .add (d j) (ordinalHeadClosure (h ⟨j.val, hm⟩)) else d j
  refine ⟨v, originalDeltaAbstractionComposition Γ σ m p h d hd, ?_, ?_⟩
  · intro j
    dsimp only [v]
    split
    · rename_i hm
      exact .add (gd j) (originalHeadClosureGrade Γ σ j.val _ (hg ⟨j.val, hm⟩))
    · exact gd j
  · apply (originalBoundedVectorSupportBridge Γ _ v).mp
    intro ρ j
    have hv0 : v 0 = .add (d 0) (ordinalHeadClosure (h 0)) := by simp [v]
    rw [hv0, add_norm]
    by_cases hj : j.val < m + 1
    · simp only [v, dif_pos hj]
      rw [add_norm]
      exact Nat.add_le_add (bd' ρ j) (bh ρ ⟨j.val, hj⟩)
    · simp only [v, dif_neg hj]
      exact (bd' ρ j).trans (Nat.le_add_right _ _)

end LogicLineages.OrdinalComparison.Source.OriginalDomain
