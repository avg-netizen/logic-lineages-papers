module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBasePublishedPackage.RetentionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBasePublishedPackage.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence




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

  obtain ⟨pF0,pR,c,tagCK,tagG,carrierTag,peelTag,baseProducerTag,
    hcal,hA,hSyntax,hInstall,hFixed,hGInstall,h6,h8,h10,h12,hcarrier,hpeel,hproducer,hinstalled,I,seedBound,hpeels⟩ :=
    RetainedBaseProducerInstallation.StatementChecks.exactInstalled f lhs rhs 2 t old oldA baseX hbase hq pCK hCK pG
  let pF := RetainedBaseProducerInstallation.selected f lhs rhs t old oldA baseX pF0 pCK pG
  have hret := RetentionProof.retained logical arithmetic axiomProgram hleaves offset hoff pF pR c tagCK pCK tagG pG
    hA hSyntax hCK hInstall hFixed hG hGInstall
  let mtag := I.previous.previous.previous.previous.previous.mpTag
  have hm : (nodes (CumulativePropositionalSource.root f lhs rhs pF pR old oldA baseX))[mtag]? =
    some ⟨4,LiteralRawMP.constructor⟩ := I.previous.previous.previous.previous.previous.hmp
  obtain ⟨xtag,hpackages⟩ := CumulativePropositionalSource.PackageProof.packages f lhs rhs old oldA baseX offset
    pF pR c tagCK pCK tagG pG mtag hret hm
  have hliteral := RetainedBaseLiteralBinary.StatementChecks.exactLiteral f lhs rhs old oldA baseX pF0 pR pCK pG c
    hA hbase I carrierTag peelTag baseProducerTag hcarrier hpeel hproducer
  exact ⟨old,oldA,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,carrierTag,peelTag,baseProducerTag,
    I,hold,holdA,hbase,hcal,hret,hpackages,hm,h12,hcarrier,hpeel,hproducer,hinstalled,hliteral⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBasePublishedPackage.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBasePublishedPackage.Proof
