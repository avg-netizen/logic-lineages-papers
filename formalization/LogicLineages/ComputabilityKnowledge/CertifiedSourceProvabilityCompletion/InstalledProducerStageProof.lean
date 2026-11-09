module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerRegistryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralTransportProof

@[expose] public section
/-! ONE actual source stage for every generated computation certificate.
The final source equations are externally indexed CLOSED arithmetic proofs;
no internal universal verifier-correctness rule is inferred. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.StageProof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof

private theorem registryIntoStage (pF pR : Program 1) (q : Program 5) (c : Code) (fuel : Nat)
    (hstage : ∀ sigma : Sentence, S pF pR q sigma ↔
      GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma) :
    ∀ raw, EffectiveNumeral.registryAxiomCheck
        (GorbowSourceRegistryPadding.root (augmented pF q) pR) raw = true →
      GorbowEnumeratedProvability.axiomCheck (c,fuel) raw = true := by
  intro raw h
  change decide (raw ∈ (GorbowPRDefiningEquations.axioms
    (GorbowSourceRegistryPadding.root (augmented pF q) pR)).map GorbowFormulaPrefixCode.encode) = true at h
  rw [decide_eq_true_eq] at h
  obtain ⟨sigma,hsigma,he⟩ := List.mem_map.mp h
  have hnamed : GorbowNamedDefiningTheory.Theory (augmented pF q) pR sigma :=
    List.mem_append_left _ hsigma
  have hS : S pF pR q sigma := List.mem_append_left _ hnamed
  have hb := (hstage sigma).mp hS
  change GorbowEnumeratedProvability.axiomCheck (c,fuel)
    (GorbowFormulaPrefixCode.encode sigma) = true at hb
  simpa only [he] using hb

/-- The same bound is chosen before all five-input numerical computations. -/
theorem generatedAtOneStage (pF pR : Program 1) (q : Program 5) (c : Code) (pG : Program 6)
    (hA : Actual pF pR q c) (hG : ProducerFor q pG) :
    ∃ fuel : Nat,
      (∀ sigma : Sentence, S pF pR q sigma ↔
        GorbowEnumeratedProvability.boundedTheory (c,fuel) sigma) ∧
      ∀ inputs : List.Vector Nat 5,
        evaluate q (GorbowEnumeratedProvability.arguments c fuel 0
          (generatedFormulaCode pF q inputs) (generatedCertificate pF pG inputs)) = 1 ∧
        Nonempty (Derivation (S pF pR q) (FiniteSource.checkerEquation pF c fuel
          (generatedFormulaCode pF q inputs) (generatedCertificate pF pG inputs))) := by
  obtain ⟨fuel,hstage,_,_⟩ := FiniteSource.Proof.actualFixedFuelPackage pF pR q c hA
  refine ⟨fuel,hstage,?_⟩
  intro inputs
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let tag := GorbowNamedInternalProvability.checkerTag pF
  have htag := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  have hregistry := hG 4 root tag htag inputs
  have hbounded : GorbowEnumeratedProvability.check (c,fuel) 0
      (generatedFormulaCode pF q inputs) (generatedCertificate pF pG inputs) = true :=
    EffectiveNumeral.Transport.numericMonotonicity _ _ (registryIntoStage pF pR q c fuel hstage)
      0 _ _ hregistry
  have hv : evaluate q (GorbowEnumeratedProvability.arguments c fuel 0
      (generatedFormulaCode pF q inputs) (generatedCertificate pF pG inputs)) = 1 := by
    rw [hA.2.1 c fuel 0 (generatedFormulaCode pF q inputs)
      (generatedCertificate pF pG inputs), hbounded]
    rfl
  refine ⟨hv,?_⟩
  obtain ⟨dn⟩ := (GorbowNamedInternalProvability.Proof.numeralCertificates 5 pF pR q
    (GorbowEnumeratedProvability.arguments c fuel 0 (generatedFormulaCode pF q inputs)
      (generatedCertificate pF pG inputs))).1
  rw [hv] at dn
  have dn' : Derivation (GorbowNamedDefiningTheory.Theory (augmented pF q) pR)
      (FiniteSource.checkerEquation pF c fuel (generatedFormulaCode pF q inputs)
        (generatedCertificate pF pG inputs)) := dn
  exact GorbowTheoryProofProof.monotonicity _ (S pF pR q)
    (fun _ h => List.mem_append_left _ h) 0 _ ⟨dn'⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.StageProof
