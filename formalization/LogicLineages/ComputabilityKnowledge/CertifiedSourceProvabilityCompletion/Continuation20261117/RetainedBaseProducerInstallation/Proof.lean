module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.RegistryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence


theorem exactInstalled : Targets.Installed := by
 intro f lhs rhs k t old a baseX hbase hq pCK hCK pG
 obtain ⟨_,_,pF0,pR,hF,hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
 let ext := extra f lhs rhs t old a baseX pF0
 let box := InstalledProducerExtra.container pG ext
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let pF := selected f lhs rhs t old a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 have hcal0 : GorbowSelectedDistribution.Calibrated pF0 pR := ⟨hF,hR⟩
 have hcal1 := GorbowNamedInternalProvability.Proof.preservesCalibration 2 pF0 pR pCK hcal0
 have hcal : GorbowSelectedDistribution.Calibrated pF pR :=
  GorbowNamedInternalProvability.Proof.preservesCalibration 6 inner pR box hcal1
 obtain ⟨c,hc⟩ := (GorbowPublishedDCB.Proof.finiteSPresentation pF pR q).2
 have hA : Actual pF pR q c := ⟨hcal,hq,hc⟩
 have hCKocc : Occurs ⟨2,pCK⟩ root := RegistryProof.inSource pF pR q _
  (RegistryProof.preserved inner box _ (RegistryProof.inserted pF0 pCK))
 have hboxocc : Occurs ⟨6,box⟩ root :=
  RegistryProof.inSource pF pR q _ (RegistryProof.inserted inner box)
 obtain ⟨tagCK,_,hCKnode⟩ := (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp hCKocc
 obtain ⟨boxTag,_,hboxnode⟩ := (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp hboxocc
 obtain ⟨hGnode,hext⟩ := RegistryProof.containerExtra root boxTag pG ext hboxnode
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩,
   ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩,
   ⟨3,RuntimeOffsetAugmentationProducer.program⟩] 4 root
   (InstalledProducerExtra.extraTag boxTag pG ext) hext
 obtain ⟨cumulativeTag,hcumulative⟩ := hall ⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩ (by simp)
 obtain ⟨carrierTag,hcarrier⟩ := hall ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ (by simp)
 obtain ⟨peelTag,hpeel⟩ := hall ⟨3,RuntimeOffsetAugmentationProducer.program⟩ (by simp)
 obtain ⟨mtag,btag,I,hI⟩ := CumulativePropositionalSource.InstallationProof.installed f lhs rhs t old a baseX pF pR cumulativeTag hcumulative
 have h6 : (nodes root)[6]? = some ⟨1,augmented pF q⟩ :=
  GorbowSourceRegistryPadding.Proof.functionRoot (augmented pF q) pR
 have h8 : (nodes root)[8]? = some ⟨1,pF⟩ := RegistryProof.firstChild root 6 pF q h6
 have h10 : (nodes root)[10]? = some ⟨1,inner⟩ := RegistryProof.firstChild root 8 inner box h8
 have h12 : (nodes root)[12]? = some ⟨1,pF0⟩ := RegistryProof.firstChild root 10 pF0 pCK h10
 obtain ⟨baseProducerTag,hproducer,hinstalled⟩ :=
  CurrentStructuralProducerInventory.StatementChecks.exactInstallations 4 root f lhs rhs k t old a baseX I
   1 pF0 carrierTag hcarrier 1 pF0 (.here pF0 rfl) 12 h12
 obtain ⟨bound,hpeels⟩ := RuntimeOffsetAugmentationProducer.SourceEndpoint.exactSource
  f lhs rhs k t old a baseX pF pR c hA hbase I
 refine ⟨pF0,pR,c,tagCK,InstalledProducerExtra.producerTag boxTag pG ext,carrierTag,peelTag,baseProducerTag,
  hcal0,hA,SourceBaseCompletion.Proof.actualSyntaxAdequacy pF pR q c hA,hCKnode,
  GorbowUniformCommonKnowledge.Proof.closedFixedPoint pF pR q c tagCK pCK hA hCK hCKnode,
  hGnode,h6,h8,h10,h12,hcarrier,hpeel,hproducer,hinstalled,I,bound,?_⟩
 intro ctx value fuel
 exact ⟨hpeels 5 pF q 6 peelTag h6 hpeel ctx value fuel,
  hpeels 6 inner box 8 peelTag h8 hpeel ctx value fuel,
  hpeels 2 pF0 pCK 10 peelTag h10 hpeel ctx value fuel⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Proof
