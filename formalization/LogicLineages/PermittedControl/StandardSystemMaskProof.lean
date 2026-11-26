module
public import LogicLineages.PermittedControl.StandardSystemReductionProof
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSystemMask.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedSystemReduction SelectedPolynomialPatterns
open Source.AdmissibleSum SourcePolynomialRealization SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion (System PolynomialSolves PolynomialSatisfiable masks restrictSystem)

 theorem projectionCalibration : ProjectionCalibration :=
  SelectedPolynomialPatterns.Proof.projectionCalibration
 theorem sharedPolynomialLift : SharedPolynomialLift :=
  SelectedPolynomialPatterns.Proof.sharedPolynomialLift Phi
 theorem actualProjection : ActualProjection :=
  SelectedPolynomialPatterns.Proof.actualProjection Phi
 theorem simultaneousPatterns : SimultaneousPatterns :=
  SelectedPolynomialPatterns.Proof.simultaneousPatterns Phi
 theorem allMaskQueries : AllMaskQueries := by
  intro policy n s
  have he := simultaneousPatterns n s
  constructor
  · constructor
    · intro hn z hz
      apply (queryComplements  policy n (restrictSystem z s)).1.mpr
      intro h
      exact hn (he.mpr ⟨z,hz,h⟩)
    · intro hall hs
      obtain ⟨z,hz,ρ,hρ⟩ := he.mp hs
      exact ((queryComplements  policy n _).1.mp
        (hall z hz)) ⟨ρ,hρ⟩
  · constructor
    · intro hn z hz
      apply (queryComplements  policy n (restrictSystem z s)).2.mpr
      intro h
      exact hn (he.mpr ⟨z,hz,h⟩)
    · intro hall hs
      obtain ⟨z,hz,ρ,hρ⟩ := he.mp hs
      exact ((queryComplements  policy n _).2.mp
        (hall z hz)) ⟨ρ,hρ⟩


theorem standardSystemMask : StandardSystemMask :=
  ⟨actualRenaming,valuationPreservingSystem,systemEquality,queryComplements,levelTwoBounds,
    projectionCalibration,sharedPolynomialLift,actualProjection,simultaneousPatterns,allMaskQueries⟩
end LogicLineages.PermittedControl.StandardSystemMask.Proof
