module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SourceEndpoint
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open SixSol20261112 SixSol20261113.LiteralCheckerAuxiliaries
open LiteralSourceCoreMP (valid)
theorem exactSource : Targets.OneSource := by
  intro f lhs rhs
  let t := CurrentNamedHeaderCertificate.template
  obtain ⟨oldValid,old,oldA,baseX,oldLeaves⟩ := HistoryDispatcher.LeavesProof.constructLeaves
  have hold : ∀ v, evaluate old v = HistoryDispatcher.logicalFunction v := oldLeaves.2.1
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
    SelectionProof.registry q hq pCK hCK pG (extra f lhs rhs old oldA baseX)
  let pF := selected f lhs rhs old oldA baseX pF0 pCK pG
  let root := CumulativePropositionalSource.root f lhs rhs pF pR old oldA baseX
  let box := InstalledProducerExtra.container pG (extra f lhs rhs old oldA baseX pF0)
  have hall := ReflexivityInstalled.BundleProof.bundleInstallation
    [⟨6,RetainedBaseProducerInstallation.extra f lhs rhs t old oldA baseX pF0⟩,⟨5,program pF0⟩] 4 root extraTag hExtra
  obtain ⟨baseExtraTag,hbaseExtra⟩ := hall ⟨6,RetainedBaseProducerInstallation.extra f lhs rhs t old oldA baseX pF0⟩ (by simp)
  obtain ⟨producerTag,hproducer⟩ := hall ⟨5,program pF0⟩ (by simp)
  have hbaseAll := ReflexivityInstalled.BundleProof.bundleInstallation
    [⟨6,CumulativePropositionalSource.extra f lhs rhs t old oldA baseX⟩,
     ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old oldA baseX pF0⟩,
     ⟨3,RuntimeOffsetAugmentationProducer.program⟩] 4 root baseExtraTag hbaseExtra
  obtain ⟨cumulativeTag,hcumulative⟩ := hbaseAll ⟨6,CumulativePropositionalSource.extra f lhs rhs t old oldA baseX⟩ (by simp)
  obtain ⟨carrierTag,hcarrier⟩ := hbaseAll ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old oldA baseX pF0⟩ (by simp)
  obtain ⟨peelTag,hpeel⟩ := hbaseAll ⟨3,RuntimeOffsetAugmentationProducer.program⟩ (by simp)
  obtain ⟨oldMtag,btag,I,hI⟩ := CumulativePropositionalSource.InstallationProof.installed f lhs rhs t old oldA baseX pF pR cumulativeTag hcumulative
  obtain ⟨h6,h8,h10,h12⟩ := BoxNodes.nodes f lhs rhs t old oldA baseX pF0 pR pCK box
  obtain ⟨baseProducerTag,hbaseProducer,hbaseInstalled⟩ :=
    CurrentStructuralProducerInventory.StatementChecks.exactInstallations 4 root f lhs rhs 2 t old oldA baseX I
      1 pF0 carrierTag hcarrier 1 pF0 (.here pF0 rfl) 12 h12
  have hret := RetainedBasePublishedPackage.RetentionProof.retained logical arithmetic axiomProgram hleaves offset hoff pF pR c tagCK pCK tagG pG
    hA hSyntax hCK hInstall hFixed hG hGInstall
  let mtag := I.previous.previous.previous.previous.previous.mpTag
  have hm : (nodes root)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := I.previous.previous.previous.previous.previous.hmp
  obtain ⟨xtag,hpackages⟩ := CumulativePropositionalSource.PackageProof.packages f lhs rhs old oldA baseX offset
    pF pR c tagCK pCK tagG pG mtag hret hm
  have hliteral := SourceEndpoint.bridge f lhs rhs old oldA baseX pF0 pR pCK pG c
    hA hbase I carrierTag peelTag baseProducerTag producerTag hcarrier hpeel hbaseProducer hproducer
  exact ⟨old,oldA,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,carrierTag,peelTag,baseProducerTag,producerTag,
    I,hold,holdA,hbase,hcal,hret,hpackages,hm,h12,hcarrier,hpeel,hbaseProducer,hproducer,hliteral⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Proof
