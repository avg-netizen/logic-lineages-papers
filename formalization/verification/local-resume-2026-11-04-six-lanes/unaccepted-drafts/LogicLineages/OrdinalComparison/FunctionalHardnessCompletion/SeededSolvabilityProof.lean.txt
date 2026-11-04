module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededCompilerProof
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingProof
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Proof
open OriginalDomain SignedPair SourcePolynomialRealization SourceFiniteExponentProjection

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

private theorem seeded_grade_realization (p : NonnegativePolynomial) :
    ∃ t : ClosedExpression, ClosedGrade 1 t ∧
      signedCNF (closedValue t)=embeddedCoefficients p+signedCNF OmegaSeed.omega := by
  by_cases hp : p=0
  · refine ⟨OmegaSeed.omegaExpression,OmegaSeed.Proof.omega_graded,?_⟩
    simp [hp,embeddedCoefficients,signedCoefficients,OmegaSeed.omega]
  · obtain ⟨t,ht,hcnf,_,_⟩ := SourcePolynomialGradeOne.Proof.actualGradedRealization p hp
    refine ⟨.add t OmegaSeed.omegaExpression,.add ht OmegaSeed.Proof.omega_graded,?_⟩
    change signedCNF (ordinalNaturalSum (closedValue t) OmegaSeed.omega)=_
    rw [SignedPair.Proof.cnf_sum,hcnf]

private def emptySubstitution : AdmissibleSubstitution [] where
  vector := fun x => nomatch x
  graded := by intro τ x; cases x
  bounded := by intro τ x; cases x

/-- The same shared family is lifted at once, including zero polynomial
entries. Every new vector uses the actual norm-padding admissibility supplier. -/
theorem seeded_family (n : Nat) (p : Fin n → NonnegativePolynomial) :
    ∃ ρ : AdmissibleSubstitution (Context n),
      ∀ i, signedCNF (inputs ρ i)=embeddedCoefficients (p i)+signedCNF OmegaSeed.omega := by
  induction n with
  | zero => exact ⟨emptySubstitution,fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨τ,hτ⟩ := ih (fun i => p i.succ)
      obtain ⟨t,ht,hcnf⟩ := seeded_grade_realization (p 0)
      obtain ⟨σ,hs,hpres⟩ := SourceUnaryNormPadding.Proof.admissibleExtension _ τ t ht
      have hhead : closedValue (σ.vector .here 1)=closedValue t :=
        (congrArg closedValue (hs 1)).trans (SourceUnaryNormPadding.Proof.exactVector t ht).2.2.2
      refine ⟨σ,?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [inputs,inputVariable,Fin.cases_zero,hhead] using hcnf
      · simpa only [inputs,inputVariable,Fin.cases_succ,hpres] using hτ j

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

theorem exactSeededSatisfiability : Targets.ExactSeededSatisfiability := by
  intro n s
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨ρ,hρ⟩ := seeded_family n p
    refine ⟨ρ,?_⟩
    intro d hd
    have hf : (fun i => signedCNF (inputs ρ i)-signedCNF OmegaSeed.omega)=
        (fun i => embeddedCoefficients (p i)) := by
      funext i
      rw [hρ i]
      abel
    rw [seededInputs_eq_lastCases,exactSeedSubstitution,hf,embedding_meaning,
      hp d hd,map_zero]
  · rintro ⟨ρ,hρ⟩
    refine ⟨fun i => projectedPolynomial (inputs ρ i),?_⟩
    intro d hd
    have he := hρ d hd
    rw [seededInputs_eq_lastCases,exactSeedSubstitution] at he
    have hproj := congrArg finitePart he
    rw [linear_projection,SourceFiniteExponentProjection.Proof.signedOperations.1] at hproj
    have hseed : finitePart (signedCNF OmegaSeed.omega)=0 :=
      OmegaSeed.Proof.exactClosedSeed.2.2.2.2
    have hf : (fun i => finitePart (signedCNF (inputs ρ i)-signedCNF OmegaSeed.omega))=
        (fun i => signedCoefficients (projectedPolynomial (inputs ρ i))) := by
      funext i
      rw [sub_eq_add_neg,SourceFiniteExponentProjection.Proof.signedOperations.2.1,
        SourceFiniteExponentProjection.Proof.signedOperations.2.2.1,hseed,neg_zero,add_zero,
        projected_coefficients]
    rw [hf] at hproj
    exact hproj

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Proof
