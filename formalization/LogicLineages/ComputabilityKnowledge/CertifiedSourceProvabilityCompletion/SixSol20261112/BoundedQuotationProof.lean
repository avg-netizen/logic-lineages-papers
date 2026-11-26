module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedQuotationTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomProof
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedQuotationProof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof
open GorbowFormulaSubstitution GorbowSortedSyntaxCode

private theorem quotedConclusion (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (sigma : Sentence) (fuel cert : Nat)
    (hcheck : GorbowEnumeratedProvability.check (c,fuel) 0
      (formulaCode (.imp (rho pF c) sigma)) cert = true) :
    Nonempty (Derivation (S pF pR q) (prD pF c (prD pF c sigma))) := by
  obtain ⟨phi, hcode, hp⟩ := (GorbowEnumeratedProvability.Proof.exactNumericAcceptance c 0
    (formulaCode (.imp (rho pF c) sigma))).mp ⟨fuel, cert, hcheck⟩
  have he : phi = Formula.imp (rho pF c) sigma :=
    GorbowSortedSyntaxCodeProof.actualInjection.1 0 _ _ hcode.symm
  subst phi
  rw [hA.2.2] at hp
  have hD : Nonempty (Derivation (D pF pR q c) sigma) :=
    (GorbowClosedDeductionProof.closedExtension (S pF pR q) (rho pF c) sigma).mpr hp
  have hPr := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA sigma hD
  exact HBAxiomProof.certificationInS pF pR q c hA (prD pF c sigma) hPr

private theorem closedQuotation (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (sigma : Sentence) (fuel cert : Nat) :
    Nonempty (Derivation (S pF pR q)
      (.imp (FiniteSource.checkerEquation pF c fuel
        (formulaCode (.imp (rho pF c) sigma)) cert) (prD pF c (prD pF c sigma)))) := by
  let T := S pF pR q
  let f := formulaCode (.imp (rho pF c) sigma)
  let P := FiniteSource.checkerEquation pF c fuel f cert
  let R := prD pF c (prD pF c sigma)
  by_cases hcheck : GorbowEnumeratedProvability.check (c,fuel) 0 f cert = true
  · obtain ⟨hr⟩ := quotedConclusion pF pR q c hA sigma fuel cert hcheck
    exact ⟨Hilbert.lift P hr⟩
  · have hf : GorbowEnumeratedProvability.check (c,fuel) 0 f cert = false :=
      Bool.eq_false_iff.mpr hcheck
    have hv : evaluate q (GorbowEnumeratedProvability.arguments c fuel 0 f cert) ≠ 1 := by
      rw [hA.2.1 c fuel 0 f cert, hf]
      decide
    obtain ⟨hn⟩ := (GorbowNamedInternalProvability.Proof.numeralCertificates
      5 pF pR q (GorbowEnumeratedProvability.arguments c fuel 0 f cert)).2 1 hv
    obtain ⟨hnS⟩ := GorbowTheoryProofProof.monotonicity _ T
      (fun _ h => List.mem_append_left _ h) 0 _ ⟨hn⟩
    have h : Hilbert.Local T 0 [P] R :=
      Hilbert.Local.explosion R (.hypothesis List.mem_cons_self) (.base hnS)
    exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

private theorem weakenInstance (phi : Sentence) (cert : Nat) :
    substituteFormula (Fin.cases (Term.numeral cert) Term.var : Fin 1 → Term 0)
      (weakenClosed 1 phi) = phi := by
  unfold weakenClosed
  rw [GorbowFormulaCompositionProof.composition]
  have he : (fun i : Fin 0 => GorbowSubstitution.substitute
      (Fin.cases (Term.numeral cert) Term.var : Fin 1 → Term 0)
      ((Fin.elim0 : Fin 0 → Term 1) i)) = (Fin.elim0 : Fin 0 → Term 0) := by
    funext i
    exact Fin.elim0 i
  rw [he]
  exact GorbowClosedDeductionProof.closedSyntax.1 phi

private theorem matrixInstance (pF : Program 1) (c : Code) (sigma : Sentence)
    (fuel cert : Nat) :
    GorbowStandardInstances.instantiate
      (.imp (BoundedMP.checkerAt pF c fuel
        (formulaCode (.imp (rho pF c) sigma)) (.var 0))
        (weakenClosed 1 (prD pF c (prD pF c sigma)))) (Term.numeral cert) =
      .imp (FiniteSource.checkerEquation pF c fuel
        (formulaCode (.imp (rho pF c) sigma)) cert) (prD pF c (prD pF c sigma)) := by
  unfold GorbowStandardInstances.instantiate
  rw [substituteFormula, weakenInstance]
  congr 1
  simp only [BoundedMP.checkerAt, substituteFormula,
    GorbowPRCallCongruence.Proof.callSubstitution, GorbowHeaderSubstitutionProof.numerals,
    List.Vector.map_cons, List.Vector.map_nil, GorbowSubstitution.substitute]
  rfl

theorem boundedSourceQuotation : BoundedQuotationTargets.BoundedSourceQuotation := by
  intro pF pR q c hA sigma fuel bound
  apply SourceBaseCompletion.BoundedRange.Proof.boundedGeneralization (S pF pR q) 0 bound
    (.imp (BoundedMP.checkerAt pF c fuel
      (formulaCode (.imp (rho pF c) sigma)) (.var 0))
      (weakenClosed 1 (prD pF c (prD pF c sigma))))
  intro i
  rw [matrixInstance]
  exact closedQuotation pF pR q c hA sigma fuel i.val

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedQuotationProof
