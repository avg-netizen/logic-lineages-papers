module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.NodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.NodeProof
open GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB HistoryRuleSuffix
open SixSol20261112 LiteralCheckerAuxiliaries

private theorem ruleNo {packed : Packed} (r : Nat) {yes no : Program 4} (h : Occurs packed no) :
 Occurs packed (HistoryDispatcher.ruleSelect r yes no) := .compositionArgument HistoryCodec.select _ 1 h
private theorem ruleYes {packed : Packed} (r : Nat) {yes no : Program 4} (h : Occurs packed yes) :
 Occurs packed (HistoryDispatcher.ruleSelect r yes no) := .compositionArgument HistoryCodec.select _ 2 h

theorem dispatcherAxiom (v l a : Program 1) (x : Program 3) :
 Occurs ⟨3,x⟩ (HistoryDispatcher.lineDispatcher v l a x) := by
 have hx : Occurs ⟨3,x⟩ (.composition x HistoryDispatcher.axiomArguments) := .compositionFunction x _ (.here _ rfl)
 have hr : Occurs ⟨3,x⟩ (HistoryDispatcher.ruleDispatcher l a x) :=
  ruleNo 0 (ruleNo 1 (ruleNo 2 (ruleNo 3 (ruleYes 4 hx))))
 exact .compositionArgument HistoryCodec.select _ 2 hr

theorem actualAxiom (l a : Program 1) (baseX : Program 3) (pF pR : Program 1) :
 ∃ xtag : Nat, (nodes (GorbowSourceRegistryPadding.root
  (augmented pF (LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer)) pR))[xtag]? =
  some (⟨3,SaturatedAxiomLeaf.saturated baseX⟩ : Packed) := by
 let x := SaturatedAxiomLeaf.saturated baseX
 let v := LiteralSourceCoreMP.valid
 let q0 := LiteralKernelSource.coreChecker v l a x bound initial finalizer
 let q := LiteralKernelSource.verifier v l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let ktag := LiteralKernelSource.kernelTag pF v l a x bound initial finalizer
 let dtag := LiteralSourceCoreMP.dispatcherTag pF l a x
 have ht : (nodes root)[GorbowNamedInternalProvability.checkerTag pF]? = some ⟨5,Fuel.verifier q0⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 have hk := LiteralKernelSource.InstallationProof.kernelInstalled root _ v l a x bound initial finalizer ht
 have hd : (nodes root)[dtag]? = some ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ :=
  LiteralSourceCoreMP.NodeProof.dispatcherInstalled root ktag l a x hk
 obtain ⟨offset,_,hoff⟩ := (GorbowPRRegistry.Proof.taggedCoverage 4 (HistoryDispatcher.lineDispatcher v l a x) ⟨3,x⟩).mp (dispatcherAxiom v l a x)
 exact ⟨dtag+offset,GorbowPRSubtree.Proof.lookupTransport 4 root dtag ⟨4,HistoryDispatcher.lineDispatcher v l a x⟩ offset ⟨3,x⟩ hd hoff⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.NodeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.NodeProof
