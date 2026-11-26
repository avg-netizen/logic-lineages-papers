module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMPTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBCertificateMPProof
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeProof

@[expose] public section
/-! Bounded INTERNAL preservation for the actual source checker. Genuine
positive/negative numeral derivations give the finite instances, while the
paid ordinary PA finite-range proof introduces both quantified certificate
variables. External bounds/fuels are never turned into a universal bound/fuel
claim. The unchanged unbounded original HB2 and HB3 remain separate targets. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMPProof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof
open GorbowFormulaSubstitution GorbowSortedSyntaxCode BoundedMP

private theorem namedIntoS (pF pR : Program 1) (q : Program 5) :
    ∀ sigma, GorbowNamedDefiningTheory.Theory (augmented pF q) pR sigma → S pF pR q sigma :=
  fun _ h => List.mem_append_left _ h

private theorem negativeChecker (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (fuel formula cert : Nat)
    (hbad : GorbowEnumeratedProvability.check (c,fuel) 0 formula cert ≠ true) :
    Nonempty (Derivation (S pF pR q)
      (.neg (FiniteSource.checkerEquation pF c fuel formula cert))) := by
  have hf : GorbowEnumeratedProvability.check (c,fuel) 0 formula cert = false :=
    Bool.eq_false_iff.mpr hbad
  have hv : evaluate q (GorbowEnumeratedProvability.arguments c fuel 0 formula cert) ≠ 1 := by
    rw [hA.2.1 c fuel 0 formula cert, hf]
    decide
  obtain ⟨hn⟩ := (GorbowNamedInternalProvability.Proof.numeralCertificates
    5 pF pR q (GorbowEnumeratedProvability.arguments c fuel 0 formula cert)).2 1 hv
  exact GorbowTheoryProofProof.monotonicity _ (S pF pR q) (namedIntoS pF pR q) 0 _ ⟨hn⟩

private theorem certifiedConclusion (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (sigma tau : Sentence) (s t ci ca : Nat)
    (hi : GorbowEnumeratedProvability.check (c,s) 0
      (formulaCode (.imp (rho pF c) (.imp sigma tau))) ci = true)
    (ha : GorbowEnumeratedProvability.check (c,t) 0
      (formulaCode (.imp (rho pF c) sigma)) ca = true) :
    Nonempty (Derivation (S pF pR q) (prD pF c tau)) := by
  have hout := HBCertificateMP.conditionalMPMaxFuel (rho pF c) sigma tau c s t ci ca hi ha
  obtain ⟨phi, hcode, hp⟩ := (GorbowEnumeratedProvability.Proof.exactNumericAcceptance c 0
    (formulaCode (.imp (rho pF c) tau))).mp
      ⟨max s t, HBCertificateMP.conditionalMP (rho pF c) sigma tau ci ca, hout⟩
  have he : phi = Formula.imp (rho pF c) tau :=
    GorbowSortedSyntaxCodeProof.actualInjection.1 0 _ _ hcode.symm
  subst phi
  rw [hA.2.2] at hp
  have hD : Nonempty (Derivation (D pF pR q c) tau) :=
    (GorbowClosedDeductionProof.closedExtension (S pF pR q) (rho pF c) tau).mpr hp
  exact HBAxiomProof.certificationInS pF pR q c hA tau hD

private theorem closedMP (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (sigma tau : Sentence) (s t ci ca : Nat) :
    Nonempty (Derivation (S pF pR q)
      (.imp (FiniteSource.checkerEquation pF c s
        (formulaCode (.imp (rho pF c) (.imp sigma tau))) ci)
        (.imp (FiniteSource.checkerEquation pF c t
          (formulaCode (.imp (rho pF c) sigma)) ca) (prD pF c tau)))) := by
  let T := S pF pR q
  let P := FiniteSource.checkerEquation pF c s
    (formulaCode (.imp (rho pF c) (.imp sigma tau))) ci
  let Q := FiniteSource.checkerEquation pF c t (formulaCode (.imp (rho pF c) sigma)) ca
  let R := prD pF c tau
  by_cases hi : GorbowEnumeratedProvability.check (c,s) 0
      (formulaCode (.imp (rho pF c) (.imp sigma tau))) ci = true
  · by_cases ha : GorbowEnumeratedProvability.check (c,t) 0
        (formulaCode (.imp (rho pF c) sigma)) ca = true
    · obtain ⟨hr⟩ := certifiedConclusion pF pR q c hA sigma tau s t ci ca hi ha
      exact ⟨Hilbert.lift P (Hilbert.lift Q hr)⟩
    · obtain ⟨hn⟩ := negativeChecker pF pR q c hA t
        (formulaCode (.imp (rho pF c) sigma)) ca ha
      have h : Hilbert.Local T 0 [Q,P] R :=
        Hilbert.Local.explosion R (.hypothesis List.mem_cons_self) (.base hn)
      exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge h))⟩
  · obtain ⟨hn⟩ := negativeChecker pF pR q c hA s
      (formulaCode (.imp (rho pF c) (.imp sigma tau))) ci hi
    have h : Hilbert.Local T 0 [Q,P] R :=
      Hilbert.Local.explosion R
        (.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) (.base hn)
    exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge h))⟩

private theorem substituteWeakened {m n : Nat} (sub : Fin m → Term n) (phi : Sentence) :
    substituteFormula sub (weakenClosed m phi) = weakenClosed n phi := by
  unfold weakenClosed
  rw [GorbowFormulaCompositionProof.composition]
  apply congrArg (fun f : Fin 0 → Term n => substituteFormula f phi)
  funext i
  exact Fin.elim0 i

private theorem substituteChecker {m n : Nat} (sub : Fin m → Term n)
    (pF : Program 1) (c : Code) (fuel formula : Nat) (cert : Term m) :
    substituteFormula sub (checkerAt pF c fuel formula cert) =
      checkerAt pF c fuel formula (GorbowSubstitution.substitute sub cert) := by
  simp only [checkerAt, substituteFormula, GorbowPRCallCongruence.Proof.callSubstitution,
    List.Vector.map_cons, List.Vector.map_nil, GorbowHeaderSubstitutionProof.numerals]

private def row (pF : Program 1) (c : Code) (sigma tau : Sentence)
    (s t ci : Nat) : Formula 1 :=
  .imp (checkerAt pF c s (formulaCode (.imp (rho pF c) (.imp sigma tau))) (Term.numeral ci))
    (.imp (checkerAt pF c t (formulaCode (.imp (rho pF c) sigma)) (.var 0))
      (weakenClosed 1 (prD pF c tau)))

private theorem matrixInstance (pF : Program 1) (c : Code) (sigma tau : Sentence)
    (s t ci : Nat) :
    substituteFormula
      (liftSubstitute (Fin.cases (Term.numeral ci) Term.var : Fin 1 → Term 0))
      (matrix pF c sigma tau s t) = row pF c sigma tau s t ci := by
  simp only [matrix, row, substituteFormula, substituteChecker, substituteWeakened,
    GorbowSubstitution.substitute, liftSubstitute, Fin.cases_zero, Fin.cases_succ,
    renameTerm, GorbowHeaderSubstitutionProof.numerals]

private theorem rowInstance (pF : Program 1) (c : Code) (sigma tau : Sentence)
    (s t ci ca : Nat) :
    GorbowStandardInstances.instantiate (row pF c sigma tau s t ci) (Term.numeral ca) =
      .imp (FiniteSource.checkerEquation pF c s
        (formulaCode (.imp (rho pF c) (.imp sigma tau))) ci)
        (.imp (FiniteSource.checkerEquation pF c t
          (formulaCode (.imp (rho pF c) sigma)) ca) (prD pF c tau)) := by
  simp only [GorbowStandardInstances.instantiate, row, substituteFormula, substituteChecker,
    GorbowHeaderSubstitutionProof.numerals, substituteWeakened, GorbowSubstitution.substitute]
  rw [show weakenClosed 0 (prD pF c tau) = prD pF c tau from
    GorbowClosedDeductionProof.closedSyntax.1 _]
  rfl

private theorem guardInstance (bound ci : Nat) :
    substituteFormula
      (liftSubstitute (Fin.cases (Term.numeral ci) Term.var : Fin 1 → Term 0))
      (SourceBaseCompletion.BoundedRange.guard (m := 1) bound) =
      SourceBaseCompletion.BoundedRange.guard (m := 0) bound := by
  rw [SourceBaseCompletion.BoundedRange.Proof.compilerGuard 1 bound,
    SourceBaseCompletion.BoundedRange.Proof.compilerGuard 0 bound]
  simp only [SourceBaseCompletion.BoundedRange.literalGuard, substituteFormula,
    GorbowSubstitution.substitute, GorbowHeaderSubstitutionProof.numerals,
    liftSubstitute, Fin.cases_zero, Fin.cases_succ, renameTerm]

private theorem boundedInstance (pF : Program 1) (c : Code) (sigma tau : Sentence)
    (s t bound ci : Nat) :
    GorbowStandardInstances.instantiate
      (SourceBaseCompletion.BoundedRange.bounded bound (matrix pF c sigma tau s t))
      (Term.numeral ci) =
      SourceBaseCompletion.BoundedRange.bounded bound (row pF c sigma tau s t ci) := by
  unfold GorbowStandardInstances.instantiate SourceBaseCompletion.BoundedRange.bounded
  change Formula.all (.imp _ _) = Formula.all (.imp _ _)
  rw [guardInstance, matrixInstance]

theorem boundedSourceMP : BoundedMPTargets.BoundedSourceMP := by
  intro pF pR q c hA sigma tau s t boundImp boundAnte
  apply SourceBaseCompletion.BoundedRange.Proof.boundedGeneralization
    (S pF pR q) 0 boundImp
    (SourceBaseCompletion.BoundedRange.bounded boundAnte (matrix pF c sigma tau s t))
  intro i
  rw [boundedInstance]
  apply SourceBaseCompletion.BoundedRange.Proof.boundedGeneralization
    (S pF pR q) 0 boundAnte (row pF c sigma tau s t i.val)
  intro j
  rw [rowInstance]
  exact closedMP pF pR q c hA sigma tau s t i.val j.val

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMPProof
