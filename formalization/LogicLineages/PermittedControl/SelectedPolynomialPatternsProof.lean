module
public import LogicLineages.PermittedControl.SelectedPolynomialPatternsTargets
public import LogicLineages.PermittedControl.SelectedPolynomialLiftProof
public import LogicLineages.PermittedControl.SelectedSystemReductionProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PatternProof
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialPatterns.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedSystemReduction
open SourcePolynomialRealization SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion (System PolynomialSolves PolynomialSatisfiable masks restrictSystem zeroExtend)

 theorem projected_coefficients (a : Ordinal) :
    signedCoefficients (projectedPolynomial a)=finitePart (SignedPair.signedCNF a) := by
  ext n
  simp [signedCoefficients,projectedPolynomial,finitePart,SignedPair.signedCNF]

 theorem projectionCalibration : SelectedPolynomialPatternsTargets.ProjectionCalibration := by
  refine ⟨?_,projected_coefficients,?_⟩
  · intro a n
    simp [finitePart,SignedPair.signedCNF]
  · intro n x d
    have he : (fun i => signedCoefficients (projectedPolynomial (x i)))=
        (fun i => finitePart (SignedPair.signedCNF (x i))) := funext fun i => projected_coefficients _
    rw [he]
    exact (SourceFiniteExponentProjection.Proof.expressionTransport n x d).symm

private theorem embedding_shift (p : PolynomialGroup) :
    SignedPair.omegaShift (polynomialEmbedding p)=polynomialEmbedding (polynomialShift p) := by
  change Finsupp.mapDomain (fun e : Ordinal => e+1)
    (Finsupp.mapDomain (fun n : Nat => (n : Ordinal)) p)=
    Finsupp.mapDomain (fun n : Nat => (n : Ordinal)) (Finsupp.mapDomain Nat.succ p)
  rw [←Finsupp.mapDomain_comp,←Finsupp.mapDomain_comp]
  congr 1

 theorem meaning_lift {n : Nat} (x : Fin n → Ordinal) (p : Fin n → PolynomialGroup)
    (hp : ∀ i, SignedPair.signedCNF (x i)=polynomialEmbedding (p i))
    (d : SignedPair.Expression n) :
    SignedPair.meaning x d=polynomialEmbedding (polynomialMeaning p d) := by
  induction d with
  | unit =>
    simpa [SignedPair.meaning,polynomialMeaning,polynomialEmbedding,
      Finsupp.mapDomain.addMonoidHom] using SignedPair.Proof.cnf_nat 1
  | var i => exact hp i
  | add a b iha ihb => simp only [SignedPair.meaning,polynomialMeaning,iha,ihb,map_add]
  | neg a ih => simp only [SignedPair.meaning,polynomialMeaning,ih,map_neg]
  | shift a ih => simp only [SignedPair.meaning,polynomialMeaning,ih,embedding_shift]

 theorem sharedPolynomialLift : SelectedPolynomialPatternsTargets.SharedPolynomialLift := by
  intro ctrl n s p hp hs
  obtain ⟨ρ,hρ⟩ := SelectedPolynomialLift.Proof.signedInputCalibration ctrl n p hp
  refine ⟨ρ,?_⟩
  intro d hd
  rw [meaning_lift (SelectedPairCompiler.inputs ctrl ρ) (fun i => signedCoefficients (p i))
    (fun i => (hρ i).1) d,hs d hd,map_zero]

 theorem actualProjection : SelectedPolynomialPatternsTargets.ActualProjection := by
  intro ctrl n s ρ hs d hd
  rw [projectionCalibration.2.2 n (SelectedPairCompiler.inputs ctrl ρ) d,hs d hd]
  exact SourceFiniteExponentProjection.Proof.signedOperations.1

 theorem simultaneousPatterns : SelectedPolynomialPatternsTargets.SimultaneousPatterns := by
  intro ctrl n s
  constructor
  · intro h
    obtain ⟨z,hz,p,hp,hs⟩ :=
      (FunctionalHardnessCompletion.Proof.simultaneousPolynomialPatterns n s).mp h
    obtain ⟨ρ,hρ⟩ := sharedPolynomialLift ctrl n (restrictSystem z s) p hp hs
    exact ⟨z,hz,ρ,hρ⟩
  · rintro ⟨z,hz,ρ,hρ⟩
    refine ⟨zeroExtend z (fun i => projectedPolynomial (SelectedPairCompiler.inputs ctrl ρ i)),?_⟩
    exact (FunctionalHardnessCompletion.Proof.restrictSystem_solves z s _).mp
      (actualProjection ctrl n _ ρ hρ)

 theorem allMaskQueries : SelectedPolynomialPatternsTargets.AllMaskQueries := by
  intro ctrl K hc policy n s
  have he := simultaneousPatterns ctrl n s
  constructor
  · constructor
    · intro hn z hz
      apply (SelectedSystemReduction.Proof.queryComplements ctrl K hc policy n (restrictSystem z s)).1.mpr
      intro h
      exact hn (he.mpr ⟨z,hz,h⟩)
    · intro hall hs
      obtain ⟨z,hz,ρ,hρ⟩ := he.mp hs
      exact ((SelectedSystemReduction.Proof.queryComplements ctrl K hc policy n _).1.mp
        (hall z hz)) ⟨ρ,hρ⟩
  · constructor
    · intro hn z hz
      apply (SelectedSystemReduction.Proof.queryComplements ctrl K hc policy n (restrictSystem z s)).2.mpr
      intro h
      exact hn (he.mpr ⟨z,hz,h⟩)
    · intro hall hs
      obtain ⟨z,hz,ρ,hρ⟩ := he.mp hs
      exact ((SelectedSystemReduction.Proof.queryComplements ctrl K hc policy n _).2.mp
        (hall z hz)) ⟨ρ,hρ⟩

 theorem selectedPolynomialPatterns : SelectedPolynomialPatternsTargets.SelectedPolynomialPatterns :=
  ⟨projectionCalibration,sharedPolynomialLift,actualProjection,simultaneousPatterns,allMaskQueries⟩
end LogicLineages.PermittedControl.SelectedPolynomialPatterns.Proof
