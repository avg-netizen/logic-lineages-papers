module
public import LogicLineages.PermittedControl.StandardSourceFactsTargets
public import LogicLineages.PermittedControl.StandardDomainCalibrationProof
public import LogicLineages.PermittedControl.SourceScalarCalibrationProof
public import LogicLineages.OrdinalComparison.WWOriginalAssignmentNormProof
public import LogicLineages.OrdinalComparison.WWOriginalSupportProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof

@[expose] public section
namespace LogicLineages.PermittedControl.StandardSourceFacts.Proof
open OrdinalComparison Source Source.AdmissibleSum

/-- Restrict a genuine whole-context substitution to precisely the occurring support. -/
theorem full_bound {Γ : List Ty} {m : Nat} (v : OrdinalVector Γ m)
    (hb : OriginalDomain.SourceBoundedVector v)
    (ρ : OriginalDomain.AdmissibleSubstitution Γ) (j : Fin (m+1)) :
    actualOrdinalNorm (OriginalDomain.expressionValue ρ (v j)) ≤
      actualOrdinalNorm (OriginalDomain.expressionValue ρ (v 0)) := by
  have hs := OriginalDomain.originalComparisonSupportCoverage Γ (v j) (v 0)
  exact (OriginalDomain.originalSupportComparisonBridge Γ
    (OriginalDomain.comparisonSupport (v j) (v 0)) (v j) (v 0) hs.1 hs.2
    (fun x y => actualOrdinalNorm x ≤ actualOrdinalNorm y)).mpr (hb j) ρ

 theorem canonicalFacts : StandardSourceFactsTargets.CanonicalFacts := by
  intro Γ τ policy a
  obtain ⟨v,hv,hg,hb⟩ := OriginalDomain.originalSourceAssignmentBounded Γ τ policy a
  refine ⟨v,hv,fun j => (StandardDomainCalibration.Proof.ambient Γ _ _).mpr (hg j),?_⟩
  intro ρ
  let σ := StandardDomainCalibration.Proof.toOriginal ρ
  have he := (StandardDomainCalibration.Proof.expressionCalibration Γ ρ σ
    (fun _ _ _ => rfl)).2
  obtain ⟨n,hn⟩ := OriginalDomain.originalAmbientScalarFinite Γ (v 0) (hg 0) σ
  have hp := OriginalDomain.originalAmbientGradePositive Γ 0 (v 0) (hg 0) σ
  have hnpos : 0 < n := by rw [hn] at hp; exact_mod_cast hp
  have hsel : SelectedSourceDomain.expressionValue Phi ρ (v 0)=(n : Ordinal) :=
    (he (v 0)).trans hn
  have hcal := SourceScalarCalibrationProof.natural_calibration n
  refine ⟨n,hnpos,hsel,?_,?_,?_⟩
  · rw [hsel]; exact hcal.1
  · rw [hsel]; exact hcal.2
  · intro j
    rw [he (v j)]
    refine ⟨OriginalDomain.originalAmbientGradePositive Γ _ _ (hg j) σ,
      OriginalDomain.originalExpressionValueBelowEpsilonZero Γ σ _,?_⟩
    have hj := full_bound v hb σ j
    simpa only [hn,hcal.2] using hj

 theorem unaryFacts : StandardSourceFactsTargets.UnaryFacts := by
  intro Γ policy ρ a
  obtain ⟨v,hv,hg,hall⟩ := canonicalFacts Γ FunctionalDetector.unary policy a
  obtain ⟨n,hp,hn,hfin,hnorm,hcoords⟩ := hall ρ
  have h0 : SelectedHardness.value0 Phi policy ρ a=n := by
    unfold SelectedHardness.value0
    rw [hv]
    exact hfin
  have h1 : SelectedHardness.value1 Phi policy ρ a=
      SelectedSourceDomain.expressionValue Phi ρ (v 1) := by
    unfold SelectedHardness.value1
    rw [hv]
    rfl
  refine ⟨v,hv,?_,h1.symm,?_,?_,?_,?_⟩
  · rw [h0]; exact hn
  · rw [h0]; exact hp
  · rw [h1]; exact (hcoords 1).1
  · rw [h1]; exact (hcoords 1).2.1
  · rw [h1,h0]; exact (hcoords 1).2.2

 theorem groundFacts : StandardSourceFactsTargets.GroundFacts := by
  intro Γ policy ρ a
  obtain ⟨v,hv,hg,hall⟩ := canonicalFacts Γ .ground policy a
  obtain ⟨n,hp,hn,hfin,hnorm,hcoords⟩ := hall ρ
  have h0 : SelectedFunctionalDetector.groundValue Phi policy ρ a=n := by
    unfold SelectedFunctionalDetector.groundValue
    rw [hv]
    exact hfin
  refine ⟨v,hv,?_,?_⟩
  · rw [h0]; exact hn
  · rw [h0]; exact hp

 theorem numericalGrowth : StandardSourceFactsTargets.NumericalGrowth :=
  ⟨Phi_strictMono,self_lt_Phi,fun _ => le_rfl,Phi_double_tower_gap⟩

 theorem standardSourceFacts : StandardSourceFactsTargets.StandardSourceFacts :=
  ⟨canonicalFacts,unaryFacts,groundFacts,numericalGrowth⟩
end LogicLineages.PermittedControl.StandardSourceFacts.Proof
