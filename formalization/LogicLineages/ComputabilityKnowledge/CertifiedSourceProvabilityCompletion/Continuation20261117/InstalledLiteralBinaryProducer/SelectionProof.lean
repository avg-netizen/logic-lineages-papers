module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SelectionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

def selectWith (E : Program 1 → Program 6) (pF0 : Program 1) (pCK : Program 2) (pG : Program 6) : Program 1 :=
 GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK)
  (InstalledProducerExtra.container pG (E pF0))

/-- Base-only extra builder is applied before choosing the final source index.
This theorem never identifies the new tuple with any earlier selected source. -/
theorem registry (q : Program 5) (hq : UniversalVerifier q) (pCK : Program 2)
 (hCK : GorbowUniformCommonKnowledge.CodeProgram pCK) (pG : Program 6) (E : Program 1 → Program 6) :
 ∃ (pF0 pR : Program 1) (c : Code) (tagCK tagG extraTag : Nat),
 let pF := selectWith E pF0 pCK pG
 GorbowSelectedDistribution.Calibrated pF0 pR ∧ Actual pF pR q c ∧
 SourceBaseCompletion.SyntaxAdequate pF pR q ∧
 GorbowUniformCommonKnowledge.RegistryInstall pF pR q tagCK pCK ∧
 GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tagCK ∧
 InstalledProducer.RegistryInstall pF pR q tagG pG ∧
 (nodes (GorbowSourceRegistryPadding.root (augmented pF q) pR))[extraTag]? = some ⟨6,E pF0⟩ := by
 obtain ⟨_,_,pF0,pR,hF,hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
 let ext := E pF0
 let box := InstalledProducerExtra.container pG ext
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let pF := selectWith E pF0 pCK pG
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 have hcal0 : GorbowSelectedDistribution.Calibrated pF0 pR := ⟨hF,hR⟩
 have hcal1 := GorbowNamedInternalProvability.Proof.preservesCalibration 2 pF0 pR pCK hcal0
 have hcal : GorbowSelectedDistribution.Calibrated pF pR :=
  GorbowNamedInternalProvability.Proof.preservesCalibration 6 inner pR box hcal1
 obtain ⟨c,hc⟩ := (GorbowPublishedDCB.Proof.finiteSPresentation pF pR q).2
 have hA : Actual pF pR q c := ⟨hcal,hq,hc⟩
 have hCKocc : Occurs ⟨2,pCK⟩ root := RetainedBaseProducerInstallation.RegistryProof.inSource pF pR q _
  (RetainedBaseProducerInstallation.RegistryProof.preserved inner box _ (RetainedBaseProducerInstallation.RegistryProof.inserted pF0 pCK))
 have hboxocc : Occurs ⟨6,box⟩ root :=
  RetainedBaseProducerInstallation.RegistryProof.inSource pF pR q _ (RetainedBaseProducerInstallation.RegistryProof.inserted inner box)
 obtain ⟨tagCK,_,hCKnode⟩ := (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp hCKocc
 obtain ⟨boxTag,_,hboxnode⟩ := (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp hboxocc
 obtain ⟨hGnode,hext⟩ := RetainedBaseProducerInstallation.RegistryProof.containerExtra root boxTag pG ext hboxnode
 exact ⟨pF0,pR,c,tagCK,InstalledProducerExtra.producerTag boxTag pG ext,
  InstalledProducerExtra.extraTag boxTag pG ext,hcal0,hA,
  SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA,hCKnode,
  GorbowUniformCommonKnowledge.Proof.closedFixedPoint pF pR q c tagCK pCK hA hCK hCKnode,hGnode,hext⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SelectionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SelectionProof
