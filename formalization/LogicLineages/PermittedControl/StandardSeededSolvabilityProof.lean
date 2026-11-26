module
public import LogicLineages.PermittedControl.StandardSeededCompilerTargets
public import LogicLineages.PermittedControl.SelectedSeededSolvabilityProof
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSeededCompiler.Proof
open OrdinalComparison Source SelectedSourceDomain SignedPair SourcePolynomialRealization SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion
open SeededCompiler (linearMeaning subtractSeed)
open SelectedSeededCompiler (seededInputs)

/-- Pure all-ordinal subtraction algebra; the supplier has no control argument. -/
theorem seedSubstitution : StandardSeededCompiler.SeedSubstitution :=
  fun n x seed d => SelectedSeededCompiler.Proof.exactSeedSubstitution n x seed d

/-- The shared zero-inclusive family supplier quantifies every control function
and carries no selected-control hypothesis; it is applied at the displayed Phi. -/
theorem sharedSeededFamily : StandardSeededCompiler.SharedSeededFamily :=
  fun n p => SelectedSeededCompiler.Proof.seeded_family Phi n p

/-! The coefficient embedding and finite-part projection lemmas below are
reconstructed here with their exact algebraic meaning; they mention no control. -/

private noncomputable def embedding : PolynomialGroup →+ CantorGroup :=
  Finsupp.mapDomain.addMonoidHom (fun n : Nat => (n : Ordinal))

private theorem embedding_shift (p : PolynomialGroup) :
    omegaShift (embedding p)=embedding (polynomialShift p) := by
  change Finsupp.mapDomain (fun e : Ordinal => e+1)
    (Finsupp.mapDomain (fun n : Nat => (n : Ordinal)) p) =
    Finsupp.mapDomain (fun n : Nat => (n : Ordinal)) (Finsupp.mapDomain Nat.succ p)
  rw [←Finsupp.mapDomain_comp,←Finsupp.mapDomain_comp]
  congr 1

private theorem embedding_meaning {n : Nat} (p : Fin n → NonnegativePolynomial)
    (d : Expression n) :
    linearMeaning (fun i => embeddedCoefficients (p i)) d=
      embedding (polynomialMeaning (fun i => signedCoefficients (p i)) d) := by
  induction d with
  | unit =>
      simpa [linearMeaning,polynomialMeaning,embedding,Finsupp.mapDomain.addMonoidHom]
        using SignedPair.Proof.cnf_nat 1
  | var i => rfl
  | add a b ha hb => simp only [linearMeaning,polynomialMeaning,ha,hb,map_add]
  | neg a ha => simp only [linearMeaning,polynomialMeaning,ha,map_neg]
  | shift a ha => simp only [linearMeaning,polynomialMeaning,ha,embedding_shift]

private theorem linear_projection {n : Nat} (x : Fin n → CantorGroup) (d : Expression n) :
    finitePart (linearMeaning x d)=polynomialMeaning (fun i => finitePart (x i)) d := by
  induction d with
  | unit =>
      exact SourceFiniteExponentProjection.Proof.expressionTransport 0
        (fun i => Fin.elim0 i) .unit
  | var i => rfl
  | add a b ha hb =>
      change finitePart (linearMeaning x a+linearMeaning x b)=_
      rw [SourceFiniteExponentProjection.Proof.signedOperations.2.1,ha,hb]
      rfl
  | neg a ha =>
      change finitePart (-linearMeaning x a)=_
      rw [SourceFiniteExponentProjection.Proof.signedOperations.2.2.1,ha]
      rfl
  | shift a ha =>
      change finitePart (omegaShift (linearMeaning x a))=_
      rw [SourceFiniteExponentProjection.Proof.exactShift,ha]
      rfl

private noncomputable def projectedPolynomial (a : Ordinal) : NonnegativePolynomial :=
  (finitePart (signedCNF a)).mapRange Int.toNat (by rfl)

private theorem projected_coefficients (a : Ordinal) :
    signedCoefficients (projectedPolynomial a)=finitePart (signedCNF a) := by
  ext n
  simp [signedCoefficients,projectedPolynomial,finitePart,signedCNF]

/-- Both directions at the displayed Phi. Forward: the one shared family, exact
seed subtraction and the coefficient embedding. Reverse: an arbitrary admitted
valuation, finite-part projection of every signed equation and the vanishing
finite part of the closed seed. -/
theorem simultaneousSolvability : StandardSeededCompiler.SimultaneousSolvability := by
  intro n s
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨ρ,hρ⟩ := SelectedSeededCompiler.Proof.seeded_family Phi n p
    refine ⟨ρ,?_⟩
    intro d hd
    have hf : (fun i => signedCNF (SelectedPairCompiler.inputs Phi ρ i)-signedCNF (SelectedOmegaSeed.omega Phi))=
        (fun i => embeddedCoefficients (p i)) := by
      funext i
      rw [hρ i]
      abel
    rw [SelectedSeededCompiler.Proof.seededInputs_eq_lastCases,
      SelectedSeededCompiler.Proof.exactSeedSubstitution,hf,embedding_meaning,
      hp d hd,map_zero]
  · rintro ⟨ρ,hρ⟩
    refine ⟨fun i => projectedPolynomial (SelectedPairCompiler.inputs Phi ρ i),?_⟩
    intro d hd
    have he := hρ d hd
    rw [SelectedSeededCompiler.Proof.seededInputs_eq_lastCases,
      SelectedSeededCompiler.Proof.exactSeedSubstitution] at he
    have hproj := congrArg finitePart he
    rw [linear_projection,SourceFiniteExponentProjection.Proof.signedOperations.1] at hproj
    have hseed : finitePart (signedCNF (SelectedOmegaSeed.omega Phi))=0 :=
      (SelectedOmegaSeed.Proof.closedSeed Phi).2.2.2.2.2
    have hf : (fun i => finitePart (signedCNF (SelectedPairCompiler.inputs Phi ρ i)-signedCNF (SelectedOmegaSeed.omega Phi)))=
        (fun i => signedCoefficients (projectedPolynomial (SelectedPairCompiler.inputs Phi ρ i))) := by
      funext i
      rw [sub_eq_add_neg,SourceFiniteExponentProjection.Proof.signedOperations.2.1,
        SourceFiniteExponentProjection.Proof.signedOperations.2.2.1,hseed,neg_zero,add_zero,
        projected_coefficients]
    rw [hf] at hproj
    exact hproj
end LogicLineages.PermittedControl.StandardSeededCompiler.Proof
