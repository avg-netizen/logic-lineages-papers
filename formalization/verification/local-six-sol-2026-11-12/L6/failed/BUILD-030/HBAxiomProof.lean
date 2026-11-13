module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Proof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSourceProof

@[expose] public section
/-! The finite additional-axiom case for the ORIGINAL source Pr_D, proved
inside S itself. The proof includes rho, retains the conditional-proof code
term, explicitly builds the finite equality/disjunction proof, and only then
generalizes its symbolic code. This is not universal numeric checker MP or
quotation preservation and does not establish internal HB2/HB3. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomProof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof
open GorbowFormulaSubstitution GorbowSortedSyntaxCode
open HBAxiomTargets

private theorem instantiateProv (pF : Program 1) (c : Code) (t : Term 0) :
    GorbowStandardInstances.instantiate (provability pF c) t = applyProv pF c t := by
  have he : (Fin.cases t Term.var : Fin 1 → Term 0) = (fun _ : Fin 1 => t) := by
    funext i
    exact Fin.eq_zero i ▸ rfl
  unfold GorbowStandardInstances.instantiate applyProv
  exact congrArg (fun s : Fin 1 → Term 0 => substituteFormula s (provability pF c)) he

theorem certificationInS : CertificationInS := by
  intro pF pR q c hA sigma hD
  obtain ⟨hd⟩ := (GorbowClosedDeductionProof.closedExtension
    (S pF pR q) (rho pF c) sigma).mp hD
  obtain ⟨hcert⟩ := GorbowPublishedDCB.Proof.sProofCertification
    pF pR q c hA (.imp (rho pF c) sigma) ⟨hd⟩
  have hCal := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  obtain ⟨hcoding⟩ := (GorbowSelectedDistribution.Proof.literalCodingCertificates
    (augmented pF q) pR hCal).2 (rho pF c) sigma
  have inclusion : ∀ tau, GorbowSelectedDistribution.Theory (augmented pF q) pR tau →
      S pF pR q tau := by
    intro tau ht
    rcases ht with hnamed | hdistribution
    · exact List.mem_append_left _ hnamed
    · subst tau
      exact List.mem_append_right _ (by simp)
  obtain ⟨hcodingS⟩ := GorbowTheoryProofProof.monotonicity _ _ inclusion 0 _ ⟨hcoding⟩
  obtain ⟨hequivalence⟩ := GorbowTheoryEqualityProof.formulaEquivalence (S pF pR q)
    (provability pF c) _ _ hcodingS
  have hback := Derivation.mp (Derivation.logical (A := S pF pR q)
    (.andRight _ _)) hequivalence
  rw [instantiateProv, instantiateProv] at hback
  exact ⟨.mp hback hcert⟩

/-! The equality-case bookkeeping is kept local because the accepted
InternalFiniteSource supplier exposes only its final S/fixed-fuel endpoint.
It is reused here for the distinct original Pr_D template and rho axiom. -/

private theorem liftVariables (n : Nat) :
    liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaVariables {n : Nat} (phi : Formula n) :
    substituteFormula Term.var phi = phi := by
  induction phi <;> simp only [substituteFormula,
    GorbowSubstitution.substitute_variables, liftVariables, *]

private def closedAt (phi : Formula 1) (code : Nat) : Sentence :=
  substituteFormula (fun _ : Fin 1 => (Term.numeral code : Term 0)) phi

private def replacementMatrix (phi : Formula 1) : Formula 2 :=
  substituteFormula (fun _ : Fin 1 => (Term.var 0 : Term 2)) phi

private theorem instantiateReplacement (phi : Formula 1) (t : Term 1) :
    GorbowStandardInstances.instantiate (replacementMatrix phi) t =
      substituteFormula (fun _ : Fin 1 => t) phi := by
  unfold GorbowStandardInstances.instantiate replacementMatrix
  rw [GorbowFormulaCompositionProof.composition]
  rfl

private theorem replacementVariable (phi : Formula 1) :
    GorbowStandardInstances.instantiate (replacementMatrix phi) (Term.var 0 : Term 1) = phi := by
  rw [instantiateReplacement]
  have he : (fun _ : Fin 1 => (Term.var 0 : Term 1)) = Term.var := by
    funext i
    exact congrArg Term.var (Fin.eq_zero i).symm
  rw [he, formulaVariables]

private theorem liftClosedAt (phi : Formula 1) (code : Nat) :
    weakenClosed 1 (closedAt phi code) =
      substituteFormula (fun _ : Fin 1 => (Term.numeral code : Term 1)) phi := by
  unfold weakenClosed closedAt
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  exact GorbowHeaderSubstitutionProof.numerals _ _ _ code

private theorem numeralCase (T : Sentence → Prop) (phi : Formula 1) (code : Nat)
    (h : Nonempty (Derivation T (closedAt phi code))) :
    Nonempty (Derivation T (.imp (.equal (Term.numeral code : Term 1) (.var 0)) phi)) := by
  obtain ⟨hl⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ h 1
  rw [liftClosedAt] at hl
  have hr : Derivation T (.imp (.equal (Term.numeral code : Term 1) (.var 0))
      (.imp (substituteFormula (fun _ : Fin 1 => (Term.numeral code : Term 1)) phi) phi)) := by
    have d := Derivation.logical (A := T)
      (.equalityReplace (replacementMatrix phi) (Term.numeral code : Term 1) (.var 0))
    rw [GorbowPACore.logicalFormula, instantiateReplacement phi (Term.numeral code),
      replacementVariable] at d
    exact d
  exact ⟨Hilbert.mpUnder hr (Hilbert.lift _ hl)⟩

private theorem finiteCases (T : Sentence → Prop) (phi : Formula 1) :
    ∀ sentences : List Sentence,
    (∀ sigma ∈ sentences, Nonempty (Derivation T (closedAt phi (formulaCode sigma)))) →
    Nonempty (Derivation T (.imp (InternalFiniteSource.codeList sentences) phi)) := by
  intro sentences
  induction sentences with
  | nil =>
      intro _
      obtain ⟨hn⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
      obtain ⟨hn1⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ ⟨hn⟩ 1
      have hb : Hilbert.Local T 1 [InternalFiniteSource.codeList []]
          (InternalFiniteSource.codeList []) := .hypothesis List.mem_cons_self
      have hp : Hilbert.Local T 1 [InternalFiniteSource.codeList []] phi :=
        Hilbert.Local.explosion phi hb (.base hn1)
      exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hp)⟩
  | cons sigma rest ih =>
      intro h
      obtain ⟨head⟩ := numeralCase T phi (formulaCode sigma) (h sigma List.mem_cons_self)
      obtain ⟨tail⟩ := ih (fun tau htau => h tau (List.mem_cons_of_mem _ htau))
      exact ⟨.mp (.mp (.logical (.orElim _ _ _)) head) tail⟩

private theorem templateAt (pF : Program 1) (c : Code) (sigma : Sentence) :
    closedAt (GorbowPublishedLobReduction.provabilityTemplate pF c) (formulaCode sigma) =
      prD pF c sigma := by
  unfold closedAt GorbowPublishedLobReduction.provabilityTemplate prD applyProv
  rw [GorbowFormulaCompositionProof.composition]
  apply congrArg (fun s : Fin 1 → Term 0 => substituteFormula s (provability pF c))
  funext i
  simp only [GorbowBooleanTruth.binaryCodeTerm, GorbowSubstitution.substitute,
    GorbowHeaderSubstitutionProof.headers, List.map_cons, List.map_nil,
    GorbowHeaderSubstitutionProof.numerals]
  rfl

theorem exactAdditionalDAxioms (pF pR : Program 1) (q : Program 5) (c : Code)
    (sigma : Sentence) : D pF pR q c sigma ↔ sigma ∈ additionalDAxioms pF pR q c := by
  simp only [D, GorbowClosedDeduction.extend, S, additionalDAxioms,
    List.mem_append, List.mem_singleton]

theorem internalAdditionalDAxioms : InternalAdditionalDAxioms := by
  intro pF pR q c hA
  refine ⟨exactAdditionalDAxioms pF pR q c, ?_⟩
  have hclosed : ∀ sigma ∈ additionalDAxioms pF pR q c,
      Nonempty (Derivation (S pF pR q)
        (closedAt (GorbowPublishedLobReduction.provabilityTemplate pF c) (formulaCode sigma))) := by
    intro sigma hsigma
    have hD : Derivation (D pF pR q c) sigma := by
      have d := Derivation.axiom (A := D pF pR q c) (n := 0) sigma
        ((exactAdditionalDAxioms pF pR q c sigma).mpr hsigma)
      rw [GorbowClosedDeductionProof.closedSyntax.1] at d
      exact d
    rw [templateAt]
    exact certificationInS pF pR q c hA sigma ⟨hD⟩
  obtain ⟨hcases⟩ := finiteCases (S pF pR q)
    (GorbowPublishedLobReduction.provabilityTemplate pF c)
    (additionalDAxioms pF pR q c) hclosed
  exact ⟨.generalize hcases⟩

theorem sameSourceAdditionalDAxioms : SameSourceAdditionalDAxioms := by
  obtain ⟨pF, pR, q, c, tag, p, hA, hCode, hInstall⟩ :=
    GorbowUniformCommonKnowledge.Proof.enrichedParameters
  refine ⟨pF, pR, q, c, tag, p, hA, ?_, hCode, hInstall, ?_, ?_⟩
  · exact SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA
  · exact GorbowUniformCommonKnowledge.Proof.closedFixedPoint pF pR q c tag p hA hCode hInstall
  · exact (internalAdditionalDAxioms pF pR q c hA).2

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomProof
