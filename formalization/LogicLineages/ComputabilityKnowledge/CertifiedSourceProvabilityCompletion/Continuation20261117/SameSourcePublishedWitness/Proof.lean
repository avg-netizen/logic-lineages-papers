module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.AlignmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.SourceBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open SixSol20261112 SixSol20261113.LiteralCheckerAuxiliaries
open LiteralSourceCoreMP (valid)
theorem exactSource : Targets.Source := by
  intro f lhs rhs
  let t := CurrentNamedHeaderCertificate.template
  obtain ⟨oldValid,rawOld,oldA,baseX,oldLeaves⟩ := HistoryDispatcher.LeavesProof.constructLeaves
  let old := CurrentQuantifierLogicalSource.selectedOld rawOld
  have hraw : ∀ v, evaluate rawOld v = HistoryDispatcher.logicalFunction v := oldLeaves.2.1
  have hold : ∀ v, evaluate old v = HistoryDispatcher.logicalFunction v :=
    OriginalQuantifierLogicalExtension.StatementChecks.exactNative.2 rawOld hraw
  let arithmetic := CumulativePropositionalSource.arithmetic oldA
  have holdA : ∀ v, evaluate oldA v = HistoryDispatcher.arithmeticFunction v := oldLeaves.2.2.1
  have harithmetic : ∀ v, evaluate arithmetic v = HistoryDispatcher.arithmeticFunction v :=
    CumulativePropositionalSource.CalibrationProof.arithmeticCalibration oldA holdA
  let logical := CumulativePropositionalSource.logical f lhs rhs old
  have hlogical : ∀ v, evaluate logical v = HistoryDispatcher.logicalFunction v :=
    CumulativePropositionalSource.CalibrationProof.logicalCalibration f lhs rhs old hold
  let axiomProgram := SaturatedAxiomLeaf.saturated baseX
  have hbase : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v := oldLeaves.2.2.2
  have hsat : ∀ v, evaluate axiomProgram v = HistoryDispatcher.axiomFunction v :=
    SaturatedAxiomLeaf.StatementChecks.nativeCalibration baseX hbase
  have hleaves : HistoryDispatcher.NativeLeaves valid logical arithmetic axiomProgram :=
    ⟨LiteralSyntaxValidator.NativeProof.nativeLine,hlogical,harithmetic,hsat⟩
  have hk := HistoryKernel.NativeProof.nativeKernel valid logical arithmetic axiomProgram hleaves
  obtain ⟨hbound,hinitial,hfinal⟩ := LiteralCheckerAuxiliaries.NativeProof.nativeAuxiliaries
  obtain ⟨offset,hoff⟩ := LiteralKernelSource.OccurrenceProof.appendOffset valid logical arithmetic axiomProgram
  let k := HistoryKernel.kernel valid logical arithmetic axiomProgram
  let q0 := LiteralKernelSource.coreChecker valid logical arithmetic axiomProgram bound initial finalizer
  have hq0 : UniversalVerifier q0 :=
    SixSol20261112.HistoryMachine.NativeProof.sameNumericChecker k bound initial finalizer hk hbound hinitial hfinal
  let q := LiteralKernelSource.verifier valid logical arithmetic axiomProgram bound initial finalizer
  have hq : UniversalVerifier q := Fuel.NativeProof.sameNumericChecker q0 hq0
  obtain ⟨pCK,hCK⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨pG,hG⟩ := InstalledProducer.Proof.programProducer q



  obtain ⟨pF0,pR,c,tagCK,tagG,extraTag,hcal,hA,hSyntax,hInstall,hFixed,hGInstall,hExtra⟩ :=
    InstalledLiteralBinaryProducer.SelectionProof.registry q hq pCK hCK pG (extra f lhs rhs rawOld oldA baseX)
  let pF := selected f lhs rhs rawOld oldA baseX pF0 pCK pG
  let root := CumulativePropositionalSource.root f lhs rhs pF pR old oldA baseX
  let box := InstalledProducerExtra.container pG (extra f lhs rhs rawOld oldA baseX pF0)
  have hall := ReflexivityInstalled.BundleProof.bundleInstallation
    [⟨6,InstalledLiteralBinaryProducer.extra f lhs rhs old oldA baseX pF0⟩,
     ⟨6,CurrentPublishedProvabilityIntroduction.extra f lhs rhs t rawOld oldA baseX⟩] 4 root extraTag hExtra
  obtain ⟨literalExtraTag,hliteralExtra⟩ := hall ⟨6,InstalledLiteralBinaryProducer.extra f lhs rhs old oldA baseX pF0⟩ (by simp)
  obtain ⟨publishedExtraTag,hpublishedExtra⟩ := hall ⟨6,CurrentPublishedProvabilityIntroduction.extra f lhs rhs t rawOld oldA baseX⟩ (by simp)
  have hliteralAll := ReflexivityInstalled.BundleProof.bundleInstallation
    [⟨6,RetainedBaseProducerInstallation.extra f lhs rhs t old oldA baseX pF0⟩,
     ⟨5,InstalledLiteralBinaryProducer.program pF0⟩] 4 root literalExtraTag hliteralExtra
  obtain ⟨baseExtraTag,hbaseExtra⟩ := hliteralAll ⟨6,RetainedBaseProducerInstallation.extra f lhs rhs t old oldA baseX pF0⟩ (by simp)
  obtain ⟨literalTag,hliteral⟩ := hliteralAll ⟨5,InstalledLiteralBinaryProducer.program pF0⟩ (by simp)
  have hbaseAll := ReflexivityInstalled.BundleProof.bundleInstallation
    [⟨6,CumulativePropositionalSource.extra f lhs rhs t old oldA baseX⟩,
     ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old oldA baseX pF0⟩,
     ⟨3,RuntimeOffsetAugmentationProducer.program⟩] 4 root baseExtraTag hbaseExtra
  obtain ⟨cumulativeTag,hcumulative⟩ := hbaseAll ⟨6,CumulativePropositionalSource.extra f lhs rhs t old oldA baseX⟩ (by simp)
  obtain ⟨carrierTag,hcarrier⟩ := hbaseAll ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old oldA baseX pF0⟩ (by simp)
  obtain ⟨peelTag,hpeel⟩ := hbaseAll ⟨3,RuntimeOffsetAugmentationProducer.program⟩ (by simp)
  obtain ⟨oldMtag,btag,I,hI⟩ := CumulativePropositionalSource.InstallationProof.installed f lhs rhs t old oldA baseX pF pR cumulativeTag hcumulative
  obtain ⟨h6,h8,h10,h12⟩ := InstalledLiteralBinaryProducer.BoxNodes.nodes f lhs rhs t old oldA baseX pF0 pR pCK box
  obtain ⟨baseTag,hbaseProducer,hbaseInstalled⟩ :=
    CurrentStructuralProducerInventory.StatementChecks.exactInstallations 4 root f lhs rhs 2 t old oldA baseX I
      1 pF0 carrierTag hcarrier 1 pF0 (.here pF0 rfl) 12 h12
  obtain ⟨⟨transformExtraTag,hTransformExtra⟩,⟨publishedTag,hPublished⟩⟩ := CurrentPublishedProvabilityIntroduction.BundleProof.unpack
    root f lhs rhs t rawOld oldA baseX publishedExtraTag hpublishedExtra
  obtain ⟨⟨quantifierExtraTag,hQuantifierExtra⟩,⟨transformTag,hTransform⟩⟩ := CurrentExistentialIntroductionProgram.BundleProof.unpack
    root f lhs rhs t rawOld oldA baseX transformExtraTag hTransformExtra
  obtain ⟨⟨structuralExtraTag,hStructuralExtra⟩,hItems⟩ := CurrentQuantifierLogicalSource.BundleProof.unpack
    root f lhs rhs t rawOld oldA baseX quantifierExtraTag hQuantifierExtra
  let Q : Program 1 → Program 1 → Program 3 → Program 5 := fun old a x => CumulativePropositionalSource.verifier f lhs rhs old a x
  obtain ⟨oldExtraTag,checkerInventoryTag,ho,hInventory⟩ := CurrentStructuralProducerSource.BundleProof.unpack
    root f lhs rhs t Q old oldA baseX structuralExtraTag hStructuralExtra
  obtain ⟨evaluatorTag,checkerTag,hEvaluator,hChecker⟩ := CurrentStructuralProducerSource.InventoryProof.rootPrograms
    root f lhs rhs t old oldA baseX q checkerInventoryTag hInventory
  obtain ⟨cl,hcl⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.lineConstructor false⟩ (by simp [CurrentQuantifierLogicalSource.items])
  obtain ⟨dl,hdl⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.lineConstructor true⟩ (by simp [CurrentQuantifierLogicalSource.items])
  obtain ⟨cs,hcs⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor false⟩ (by simp [CurrentQuantifierLogicalSource.items])
  obtain ⟨ds,hds⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor true⟩ (by simp [CurrentQuantifierLogicalSource.items])
  let N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes root :=
    { lineTag := fun b => if b then dl else cl
      singletonTag := fun b => if b then ds else cs
      hline := fun b => by cases b with | false => exact hcl | true => exact hdl
      hsingle := fun b => by cases b with | false => exact hcs | true => exact hds }
  have hret := RetainedBasePublishedPackage.RetentionProof.retained logical arithmetic axiomProgram hleaves offset hoff pF pR c tagCK pCK tagG pG
    hA hSyntax hCK hInstall hFixed hG hGInstall
  let mtag := I.previous.previous.previous.previous.previous.mpTag
  have hm : (nodes root)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := I.previous.previous.previous.previous.previous.hmp
  obtain ⟨xtag,hpackages⟩ := CumulativePropositionalSource.PackageProof.packages f lhs rhs old oldA baseX offset
    pF pR c tagCK pCK tagG pG mtag hret hm
  have hbridge := SourceBridge.bridge f lhs rhs rawOld oldA baseX pF0 pR pCK box c hA hbase I N
    carrierTag peelTag baseTag checkerInventoryTag checkerTag transformTag publishedTag
    hcarrier hpeel hbaseProducer hInventory hChecker hTransform hPublished
  exact ⟨rawOld,oldA,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,carrierTag,peelTag,baseTag,checkerInventoryTag,checkerTag,literalTag,
    publishedExtraTag,transformTag,publishedTag,I,N,hraw,hold,holdA,hbase,hcal,hret,hpackages,hm,h12,hcarrier,hpeel,hbaseProducer,
    hInventory,hChecker,hliteral,hpublishedExtra,hTransform,hPublished,
    AlignmentProof.originalSyntax pF c,AlignmentProof.outputAlignment pF pR q c hA,hbridge⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.Proof
