module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducerTargets
public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeProof
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseProof

@[expose] public section
/-! Reusable source installation for GIVEN literal checker, CK and producer
ASTs. The new source index is chosen AFTER installing both retained programs. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.RegistryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB

private def withCK (pF0 : Program 1) (pCK : Program 2) : Program 1 :=
  GorbowNamedInternalProvability.augment pF0 pCK

private def withProducer (pF0 : Program 1) (pCK : Program 2) (pG : Program 6) : Program 1 :=
  GorbowNamedInternalProvability.augment (withCK pF0 pCK) pG

private theorem preserved {n : Nat} (p : Program 1) (q : Program n) (entry : Packed)
    (h : Occurs entry p) : Occurs entry (GorbowNamedInternalProvability.augment p q) :=
  .compositionArgument _ _ (0 : Fin 2) h

private theorem inserted {n : Nat} (p : Program 1) (q : Program n) :
    Occurs ⟨n,q⟩ (GorbowNamedInternalProvability.augment p q) := by
  have h : Occurs ⟨n,q⟩ (GorbowNamedInternalProvability.wrapper q) :=
    .compositionFunction _ _ (.here q rfl)
  exact .compositionArgument _ _ (1 : Fin 2) h

private theorem inSource (pF pR : Program 1) (q : Program 5) (entry : Packed)
    (h : Occurs entry pF) :
    Occurs entry (GorbowSourceRegistryPadding.root (augmented pF q) pR) := by
  have hq : Occurs entry (augmented pF q) := preserved pF q entry h
  have hw : Occurs entry (GorbowSourceRegistryPadding.wrapper (augmented pF q)) :=
    .compositionFunction _ _ hq
  exact .compositionArgument _ _ (3 : Fin 5) hw

private theorem ckOccurs (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6) (q : Program 5) :
    Occurs ⟨2,pCK⟩ (GorbowSourceRegistryPadding.root
      (augmented (withProducer pF0 pCK pG) q) pR) :=
  inSource _ _ q _ (preserved _ pG _ (inserted pF0 pCK))

private theorem producerOccurs (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6) (q : Program 5) :
    Occurs ⟨6,pG⟩ (GorbowSourceRegistryPadding.root
      (augmented (withProducer pF0 pCK pG) q) pR) :=
  inSource _ _ q _ (inserted (withCK pF0 pCK) pG)

/-- Every supplied literal producer can use this same source installer; no
internal symbolic checker-correctness property is inferred from its AST. -/
theorem actualRegistry (q : Program 5) (hq : UniversalVerifier q)
    (pCK : Program 2) (hCK : GorbowUniformCommonKnowledge.CodeProgram pCK) (pG : Program 6) :
    ∃ (pF pR : Program 1) (c : Code) (tagCK tagG : Nat),
      Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
      GorbowUniformCommonKnowledge.RegistryInstall pF pR q tagCK pCK ∧
      GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tagCK ∧
      RegistryInstall pF pR q tagG pG := by
  obtain ⟨_,_,pF0,pR,hF,hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  let pF := withProducer pF0 pCK pG
  have hcal0 : GorbowSelectedDistribution.Calibrated pF0 pR := ⟨hF,hR⟩
  have hcalCK := GorbowNamedInternalProvability.Proof.preservesCalibration 2 pF0 pR pCK hcal0
  have hcal : GorbowSelectedDistribution.Calibrated pF pR :=
    GorbowNamedInternalProvability.Proof.preservesCalibration 6 (withCK pF0 pCK) pR pG hcalCK
  obtain ⟨c,hc⟩ := (GorbowPublishedDCB.Proof.finiteSPresentation pF pR q).2
  have hA : Actual pF pR q c := ⟨hcal,hq,hc⟩
  obtain ⟨tagCK,_,hInstallCK⟩ := (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp
    (ckOccurs pF0 pR pCK pG q)
  obtain ⟨tagG,_,hInstallG⟩ := (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp
    (producerOccurs pF0 pR pCK pG q)
  refine ⟨pF,pR,c,tagCK,tagG,hA,?_,hInstallCK,?_,hInstallG⟩
  · exact SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA
  · exact GorbowUniformCommonKnowledge.Proof.closedFixedPoint pF pR q c tagCK pCK hA hCK hInstallCK

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer.RegistryProof
