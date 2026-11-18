module
public import LogicLineages.PermittedControl.SelectedSeededCompilerProof
public import LogicLineages.PermittedControl.SelectedPolynomialLiftProof
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededCompiler.Proof
open OrdinalComparison Source SelectedSourceDomain SignedPair SourcePolynomialRealization SourceFiniteExponentProjection
open Source.FunctionalHardnessCompletion
open SeededCompiler (linearMeaning subtractSeed)

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

private theorem seeded_grade_realization (ctrl : Nat → Nat) (p : NonnegativePolynomial) :
    ∃ t : ClosedExpression, ClosedGrade ctrl 1 t ∧
      signedCNF (closedValue ctrl t)=embeddedCoefficients p+signedCNF (SelectedOmegaSeed.omega ctrl) := by
  by_cases hp : p=0
  · refine ⟨OmegaSeed.omegaExpression,SelectedOmegaSeed.Proof.omega_grade ctrl,?_⟩
    simp [hp,embeddedCoefficients,signedCoefficients,SelectedOmegaSeed.omega]
  · obtain ⟨t,ht,hcnf,_,_⟩ := SelectedPolynomialLift.Proof.gradedRealization ctrl p hp
    refine ⟨.add t OmegaSeed.omegaExpression,.add ht (SelectedOmegaSeed.Proof.omega_grade ctrl),?_⟩
    change signedCNF (ordinalNaturalSum (closedValue ctrl t) (SelectedOmegaSeed.omega ctrl))=_
    rw [SignedPair.Proof.cnf_sum,hcnf]

private def emptySubstitution (ctrl : Nat → Nat) : AdmissibleSubstitution ctrl [] where
  vector := fun x => nomatch x
  graded := by intro τ x; cases x
  bounded := by intro τ x; cases x

/-- The same shared family is lifted at once, including zero polynomial
entries. Every new vector uses the actual norm-padding admissibility supplier. -/
theorem seeded_family (ctrl : Nat → Nat) (n : Nat) (p : Fin n → NonnegativePolynomial) :
    ∃ ρ : AdmissibleSubstitution ctrl (Context n),
      ∀ i, signedCNF (SelectedPairCompiler.inputs ctrl ρ i)=embeddedCoefficients (p i)+signedCNF (SelectedOmegaSeed.omega ctrl) := by
  induction n with
  | zero => exact ⟨emptySubstitution ctrl,fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨τ,hτ⟩ := ih (fun i => p i.succ)
      obtain ⟨t,ht,hcnf⟩ := seeded_grade_realization ctrl (p 0)
      obtain ⟨σ,hs,hpres⟩ := SelectedPolynomialLift.Proof.admissibleExtension ctrl _ τ t ht
      have hhead : closedValue ctrl (σ.vector .here 1)=closedValue ctrl t :=
        (congrArg (closedValue ctrl) (hs 1)).trans (SelectedPolynomialLift.Proof.exactPaddedVector ctrl t ht).2.2.2
      refine ⟨σ,?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [SelectedPairCompiler.inputs,inputVariable,Fin.cases_zero,hhead] using hcnf
      · simpa only [SelectedPairCompiler.inputs,inputVariable,Fin.cases_succ,hpres] using hτ j

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

theorem simultaneousSolvability : SelectedSeededCompilerTargets.SimultaneousSolvability := by
  intro ctrl K hc n s
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨ρ,hρ⟩ := seeded_family ctrl n p
    refine ⟨ρ,?_⟩
    intro d hd
    have hf : (fun i => signedCNF (SelectedPairCompiler.inputs ctrl ρ i)-signedCNF (SelectedOmegaSeed.omega ctrl))=
        (fun i => embeddedCoefficients (p i)) := by
      funext i
      rw [hρ i]
      abel
    rw [seededInputs_eq_lastCases,exactSeedSubstitution,hf,embedding_meaning,
      hp d hd,map_zero]
  · rintro ⟨ρ,hρ⟩
    refine ⟨fun i => projectedPolynomial (SelectedPairCompiler.inputs ctrl ρ i),?_⟩
    intro d hd
    have he := hρ d hd
    rw [seededInputs_eq_lastCases,exactSeedSubstitution] at he
    have hproj := congrArg finitePart he
    rw [linear_projection,SourceFiniteExponentProjection.Proof.signedOperations.1] at hproj
    have hseed : finitePart (signedCNF (SelectedOmegaSeed.omega ctrl))=0 :=
      (SelectedOmegaSeed.Proof.closedSeed ctrl).2.2.2.2.2
    have hf : (fun i => finitePart (signedCNF (SelectedPairCompiler.inputs ctrl ρ i)-signedCNF (SelectedOmegaSeed.omega ctrl)))=
        (fun i => signedCoefficients (projectedPolynomial (SelectedPairCompiler.inputs ctrl ρ i))) := by
      funext i
      rw [sub_eq_add_neg,SourceFiniteExponentProjection.Proof.signedOperations.2.1,
        SourceFiniteExponentProjection.Proof.signedOperations.2.2.1,hseed,neg_zero,add_zero,
        projected_coefficients]
    rw [hf] at hproj
    exact hproj

theorem sharedSeededFamily : SelectedSeededCompilerTargets.SharedSeededFamily := by
  intro ctrl K hc n p
  exact seeded_family ctrl n p

theorem selectedSeededCompiler : SelectedSeededCompilerTargets.SelectedSeededCompiler :=
  ⟨actualCompiler,exactSeedSubstitution,sharedSeededFamily,simultaneousSolvability⟩
end LogicLineages.PermittedControl.SelectedSeededCompiler.Proof
