module
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingTargets
public import LogicLineages.OrdinalComparison.SourcePolynomialGradeOneProof
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding.Proof

open OriginalDomain

theorem exactVector : Targets.ExactVector := by
  intro t ht
  have hv : closedValue (vector t 0) = ((actualOrdinalNorm (closedValue t)+1 : Nat) : Ordinal) :=
    UnitObservation.Proof.positiveValue (actualOrdinalNorm (closedValue t))
  have hn : actualOrdinalNorm (closedValue (vector t 0)) = actualOrdinalNorm (closedValue t)+1 := by
    rw [hv]
    exact (LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof.finiteNorm _).2
  refine ⟨?_, ?_, hv, rfl⟩
  · intro j
    by_cases hj : j.val = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      exact UnitObservation.positiveGrade _
    · have hj1 : j.val = 1 := by have hh := j.isLt; omega
      have he : j = 1 := Fin.ext hj1
      subst j
      exact ht
  · intro j
    by_cases hj : j.val = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      exact le_rfl
    · have hj1 : j.val = 1 := by have hh := j.isLt; omega
      have he : j = 1 := Fin.ext hj1
      subst j
      change actualOrdinalNorm (closedValue t) ≤ actualOrdinalNorm (closedValue (vector t 0))
      rw [hn]
      omega

theorem admissibleExtension : Targets.AdmissibleExtension := by
  intro Γ ρ t ht
  have hv := exactVector t ht
  let σ : AdmissibleSubstitution (FunctionalDetector.unary :: Γ) := {
    vector := fun x j => match x with
      | .here => vector t j
      | .there x => ρ.vector x j
    graded := by
      intro τ x j
      cases x with
      | here => exact hv.1 j
      | there x => exact ρ.graded x j
    bounded := by
      intro τ x j
      cases x with
      | here => exact hv.2.1 j
      | there x => exact ρ.bounded x j }
  exact ⟨σ, fun _ => rfl, fun _ _ _ => rfl⟩

theorem polynomialExtension : Targets.PolynomialExtension := by
  intro Γ ρ p hp
  obtain ⟨t, ht, hcnf, hpos, hbound⟩ :=
    SourcePolynomialGradeOne.Proof.actualGradedRealization p hp
  obtain ⟨σ, hs, hrest⟩ := admissibleExtension Γ ρ t ht
  have hv := exactVector t ht
  have hhead : closedValue (σ.vector .here 1) = closedValue t :=
    (congrArg closedValue (hs 1)).trans hv.2.2.2
  have hscalar : closedValue (σ.vector .here 0) =
      ((actualOrdinalNorm (closedValue t)+1 : Nat) : Ordinal) :=
    (congrArg closedValue (hs 0)).trans hv.2.2.1
  refine ⟨σ, ?_, ?_, ?_, ?_, hrest⟩
  · rw [hhead]
    exact hcnf
  · rw [hhead]
    exact hpos
  · rw [hhead]
    exact hbound
  · rw [hhead, hscalar]

end LogicLineages.OrdinalComparison.Source.SourceUnaryNormPadding.Proof
