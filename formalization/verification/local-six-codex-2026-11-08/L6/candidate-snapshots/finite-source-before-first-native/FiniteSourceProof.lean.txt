module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceTargets
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityStagesProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSource.Proof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof

private theorem listStage (c : Code) :
    ∀ sentences : List Sentence,
    (∀ sigma ∈ sentences, GorbowEnumeratedProvability.enumeratedTheory c sigma) →
    ∃ fuel : Nat, ∀ sigma ∈ sentences,
      GorbowEnumeratedProvability.boundedTheory (c, fuel) sigma := by
  intro sentences
  induction sentences with
  | nil =>
      intro _
      exact ⟨0, fun _ h => False.elim (by simpa using h)⟩
  | cons sigma rest ih =>
      intro h
      obtain ⟨headFuel, headAccept⟩ :=
        (GorbowEnumeratedProvability.StagesProof.exactAxiomUnion c sigma).mp
          (h sigma List.mem_cons_self)
      obtain ⟨tailFuel, tailAccept⟩ := ih
        (fun tau htau => h tau (List.mem_cons_of_mem _ htau))
      refine ⟨max headFuel tailFuel, ?_⟩
      intro tau htau
      rcases List.mem_cons.mp htau with he | htau
      · subst tau
        exact GorbowEnumeratedProvability.StagesProof.boundedMonotonicity c headFuel
          (max headFuel tailFuel) (le_max_left _ _) sigma headAccept
      · exact GorbowEnumeratedProvability.StagesProof.boundedMonotonicity c tailFuel
          (max headFuel tailFuel) (le_max_right _ _) tau (tailAccept tau htau)

private theorem namedIntoS (pF pR : Program 1) (q : Program 5) (sigma : Sentence)
    (h : GorbowNamedDefiningTheory.Theory (augmented pF q) pR sigma) : S pF pR q sigma :=
  List.mem_append.mpr (Or.inl h)

theorem actualFixedFuelPackage : Targets.ActualFixedFuelPackage := by
  intro pF pR q c hA
  have hsource : GorbowEnumeratedProvability.enumeratedTheory c = S pF pR q := hA.2.2
  obtain ⟨fuel, hstage⟩ := listStage c (axiomsS pF pR q) (fun sigma hsigma => by
    rw [hsource]
    exact hsigma)
  have hiff : ∀ sigma : Sentence, S pF pR q sigma ↔
      GorbowEnumeratedProvability.boundedTheory (c, fuel) sigma := by
    intro sigma
    constructor
    · exact hstage sigma
    · intro h
      have he := (GorbowEnumeratedProvability.StagesProof.exactAxiomUnion c sigma).mpr ⟨fuel, h⟩
      rw [hsource] at he
      exact he
  refine ⟨fuel, hiff, ?_, ?_⟩
  · intro n phi
    constructor
    · exact GorbowTheoryProofProof.monotonicity _ _ (fun sigma h => (hiff sigma).mp h) n phi
    · exact GorbowTheoryProofProof.monotonicity _ _ (fun sigma h => (hiff sigma).mpr h) n phi
  · intro sigma hsigma
    let axCheck := GorbowEnumeratedProvability.axiomCheck (c, fuel)
    have d : Derivation (n := 0) (GorbowEnumeratedProvability.boundedTheory (c, fuel)) sigma := by
      have h := Derivation.axiom (A := GorbowEnumeratedProvability.boundedTheory (c, fuel))
        (n := 0) sigma ((hiff sigma).mp hsigma)
      rw [GorbowClosedDeductionProof.closedSyntax.1] at h
      exact h
    obtain ⟨certificate, haccept⟩ :=
      (GorbowTheoryNumericCertificateProof.proofEquivalence axCheck 0
        (GorbowSortedSyntaxCode.formulaCode sigma)).mpr ⟨sigma, rfl, ⟨d⟩⟩
    have hc : GorbowEnumeratedProvability.check (c, fuel) 0
        (GorbowSortedSyntaxCode.formulaCode sigma) certificate = true := haccept
    have hv : evaluate q (GorbowEnumeratedProvability.arguments c fuel 0
        (GorbowSortedSyntaxCode.formulaCode sigma) certificate) = 1 := by
      rw [hA.2.1 c fuel 0 (GorbowSortedSyntaxCode.formulaCode sigma) certificate, hc]
      rfl
    obtain ⟨dn⟩ := (GorbowNamedInternalProvability.Proof.numeralCertificates 5 pF pR q
      (GorbowEnumeratedProvability.arguments c fuel 0
        (GorbowSortedSyntaxCode.formulaCode sigma) certificate)).1
    rw [hv] at dn
    have dn' : Derivation (GorbowNamedDefiningTheory.Theory (augmented pF q) pR)
        (checkerEquation pF c fuel (GorbowSortedSyntaxCode.formulaCode sigma) certificate) := dn
    refine ⟨certificate, hc, ?_⟩
    exact GorbowTheoryProofProof.monotonicity _ (S pF pR q) (namedIntoS pF pR q) 0 _ ⟨dn'⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSource.Proof
