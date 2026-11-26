module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.MPPackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.NumeralPackageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries
private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
 (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
   (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
 Nonempty (Derivation (S pF pR q) phi) :=
 GorbowTheoryProofProof.monotonicity _ _
   (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

theorem numeralPackage (l a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (ntag : Nat)
 (hoff : (nodes (HistoryKernel.kernel LiteralSourceCoreMP.valid l a (SaturatedAxiomLeaf.saturated baseX)))[offset]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes (GorbowSourceRegistryPadding.root
   (augmented pF (LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer)) pR))[ntag]? =
   some ⟨1,LiteralNumeralPrefix.numeralCode⟩) :
 Targets.NumeralPackage l a baseX offset pF pR ntag := by
 let x := SaturatedAxiomLeaf.saturated baseX
 let v := LiteralSourceCoreMP.valid
 let k := HistoryKernel.kernel v l a x
 let q := LiteralKernelSource.verifier v l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let fuelTag := GorbowNamedInternalProvability.checkerTag pF
 let ktag := LiteralKernelSource.kernelTag pF v l a x bound initial finalizer
 let atag := LiteralKernelSource.appendTag pF v l a x bound initial finalizer offset
 let ptag := LiteralKernelSource.pairTag pF v l a x bound initial finalizer
 let ctag := LiteralKernelSource.consTag pF v l a x bound initial finalizer
 let itag := LiteralValidatedSource.iteratorTag pF l a x
 let vtag := LiteralValidatedSource.validityTag pF l a x
 let stag := LiteralValidatedSource.scanTag vtag
 have ht : (nodes root)[fuelTag]? = some ⟨5,Fuel.verifier (LiteralKernelSource.coreChecker v l a x bound initial finalizer)⟩ :=
   GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 have hk : (nodes root)[ktag]? = some ⟨3,k⟩ :=
   LiteralKernelSource.InstallationProof.kernelInstalled root fuelTag v l a x bound initial finalizer ht
 have ha : (nodes root)[atag]? = some ⟨2,HistoryAppend.append⟩ :=
   GorbowPRSubtree.Proof.lookupTransport 4 root ktag ⟨3,k⟩ offset ⟨2,HistoryAppend.append⟩ hk hoff
 obtain ⟨hp,_,_,_,hc⟩ := HistoryKernel.OptionProof.kernelNodes root ktag v l a x hk
 have hi : (nodes root)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator k⟩ :=
   LiteralValidatedSource.NodeProof.iteratorNode pF pR l a x
 have hv : (nodes root)[vtag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩ :=
   HistoryTopProvenance.OccurrenceProof.actualValidityOccurrence v l a x 4 root itag hi
 obtain ⟨_,_,_,hs,_,_,_⟩ := LiteralValidatedSource.NodeProof.lineNodes root vtag hv
 refine ⟨hn,hs,?_,?_⟩
 · obtain ⟨h⟩ := LiteralNumeralPrefix.StatementChecks.exactScan 4 root ntag stag ptag ctag hn hs hp hc
     3 (.var 0) (.var 1) (.var 2)
   exact inSource pF pR q _ ⟨Fuel.Logic.closeAll h⟩
 · obtain ⟨h⟩ := LiteralNumeralPrefix.StatementChecks.exactContinuation 4 root ntag stag ptag ctag atag hn hs hp hc ha
     4 (.var 0) (.var 1) (.var 2) (.var 3)
   exact inSource pF pR q _ ⟨Fuel.Logic.closeAll h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.NumeralPackageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.NumeralSourceHB2.NumeralPackageProof
