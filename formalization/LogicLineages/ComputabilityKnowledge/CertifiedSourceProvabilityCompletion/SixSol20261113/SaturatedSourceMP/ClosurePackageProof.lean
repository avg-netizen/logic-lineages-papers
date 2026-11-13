module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.ClosurePackageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB List.Vector
open SixSol20261112 LiteralCheckerAuxiliaries
open LiteralSourceCoreMP (valid lengthTag dropTag lookupTag dispatcherTag coreTag)
private theorem inSource (pF pR : Program 1) (q : Program 5) {ctx : Nat} (phi : Formula ctx)
 (h : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory
   (GorbowSourceRegistryPadding.root (augmented pF q) pR)) phi)) :
 Nonempty (Derivation (S pF pR q) phi) :=
 GorbowTheoryProofProof.monotonicity _ _
   (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx phi h

theorem closurePackage (l a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (mtag : Nat)
 (hoff : (nodes (HistoryKernel.kernel valid l a (SaturatedAxiomLeaf.saturated baseX)))[offset]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes (GorbowSourceRegistryPadding.root
   (augmented pF (LiteralKernelSource.verifier valid l a (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer)) pR))[mtag]? =
   some ⟨4,LiteralRawMP.constructor⟩) :
 Targets.ClosurePackage l a baseX offset pF pR mtag := by
 let x := SaturatedAxiomLeaf.saturated baseX
 let k := HistoryKernel.kernel valid l a x
 let q0 := LiteralKernelSource.coreChecker valid l a x bound initial finalizer
 let q := LiteralKernelSource.verifier valid l a x bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 let fuelTag := GorbowNamedInternalProvability.checkerTag pF
 let ktag := LiteralKernelSource.kernelTag pF valid l a x bound initial finalizer
 let atag := LiteralKernelSource.appendTag pF valid l a x bound initial finalizer offset
 let ptag := LiteralKernelSource.pairTag pF valid l a x bound initial finalizer
 let ctag := LiteralKernelSource.consTag pF valid l a x bound initial finalizer
 let itag := LiteralValidatedSource.iteratorTag pF l a x
 let vtag := LiteralValidatedSource.validityTag pF l a x
 let stag := LiteralValidatedSource.scanTag vtag
 let dtag := HistoryIteratorDrain.rightTag pF valid l a x bound initial finalizer
 have ht : (nodes root)[fuelTag]? = some ⟨5,Fuel.verifier q0⟩ :=
   GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
 have hk : (nodes root)[ktag]? = some ⟨3,k⟩ :=
   LiteralKernelSource.InstallationProof.kernelInstalled root fuelTag valid l a x bound initial finalizer ht
 have ha : (nodes root)[atag]? = some ⟨2,HistoryAppend.append⟩ :=
   GorbowPRSubtree.Proof.lookupTransport 4 root ktag ⟨3,k⟩ offset ⟨2,HistoryAppend.append⟩ hk hoff
 obtain ⟨hp,_,_,_,hc⟩ := HistoryKernel.OptionProof.kernelNodes root ktag valid l a x hk
 have hi : (nodes root)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator k⟩ :=
   LiteralValidatedSource.NodeProof.iteratorNode pF pR l a x
 have hv : (nodes root)[vtag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩ :=
   HistoryTopProvenance.OccurrenceProof.actualValidityOccurrence valid l a x 4 root itag hi
 obtain ⟨_,_,_,hs,_,_,_⟩ := LiteralValidatedSource.NodeProof.lineNodes root vtag hv
 have hl := LiteralSourceCoreMP.NodeProof.lengthInstalled root stag hs
 obtain ⟨hr,hd⟩ := LiteralSourceCoreMP.NodeProof.appendLookupDrop root atag ha
 have hdright : (nodes root)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ :=
   HistoryIteratorDrain.InstallationProof.rightInstalled root ktag valid l a x hk
 have hdispatch := LiteralSourceCoreMP.NodeProof.dispatcherInstalled root ktag l a x hk
 have hcore := LiteralSourceCoreMP.NodeProof.coreInstalled pF pR l a x
 obtain ⟨hmono⟩ := SaturatedCoreFuel.StatementChecks.internalMonotonicity valid l a baseX 4 root
  (coreTag pF l a x) hcore 6 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
 obtain ⟨heq⟩ := SaturatedVerifierCore.StatementChecks.internalEquivalence valid l a baseX 4 root
  fuelTag (coreTag pF l a x) ht hcore 5 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
 obtain ⟨hmp⟩ := SaturatedVerifierMP.StatementChecks.internalVerifierMP l a baseX 4 root
  itag (lengthTag stag) atag ptag ctag dtag (dropTag atag) (lookupTag atag)
  (dispatcherTag pF l a x) hi hl ha hp hc hdright hd hr hdispatch
  mtag (coreTag pF l a x) fuelTag hm hcore ht 8
  (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7)
 exact ⟨inSource pF pR q (coreMonotonicityClause (coreTag pF l a x)) ⟨Fuel.Logic.closeAll hmono⟩,
  inSource pF pR q (equivalenceClause fuelTag (coreTag pF l a x)) ⟨Fuel.Logic.closeAll heq⟩,
  inSource pF pR q (outerMPClause fuelTag atag ctag mtag) ⟨Fuel.Logic.closeAll hmp⟩⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.ClosurePackageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.ClosurePackageProof
