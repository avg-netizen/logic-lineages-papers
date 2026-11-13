module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.IterationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.InstallationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112

theorem sameSourceIteratorDrain : Targets.SameSourceIteratorDrain := by
  obtain ⟨v,l,a,x,bound,initial,finalizer,offset,pF,pR,c,tagCK,pCK,tagG,pG,
    hleaves,hk,hbound,hinitial,hfinal,hoff,hq0,hA,hSyntax,hCK,hInstall,hFixed,
    hG,hGInstall,hkin,hain,hpin,hcin,hstep,hinc,hmono,hfusion,hsuffix,hiterator⟩ :=
    HistoryIteratorSuffix.SourceProof.sameSourceIteratorSuffix
  let k := HistoryKernel.kernel v l a x
  let q := LiteralKernelSource.verifier v l a x bound initial finalizer
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let fuelTag := GorbowNamedInternalProvability.checkerTag pF
  let itag := SixSol20261112.HistoryMachine.iteratorTag fuelTag k bound initial finalizer
  let atag := LiteralKernelSource.appendTag pF v l a x bound initial finalizer offset
  let ptag := LiteralKernelSource.pairTag pF v l a x bound initial finalizer
  let ctag := LiteralKernelSource.consTag pF v l a x bound initial finalizer
  let dtag := rightTag pF v l a x bound initial finalizer
  have ht : (nodes root)[fuelTag]? = some ⟨5,q⟩ := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  have hi := SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled root fuelTag k bound initial finalizer ht
  have hd : (nodes root)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ :=
    InstallationProof.rightInstalled root _ v l a x hkin
  obtain ⟨dropOffset,hdrop⟩ := InstallationProof.dropOffset
  have hdropRoot : (nodes root)[atag+dropOffset]? = some ⟨2,HistoryLookup.drop⟩ :=
    GorbowPRSubtree.Proof.lookupTransport 4 root atag ⟨2,HistoryAppend.append⟩ dropOffset ⟨2,HistoryLookup.drop⟩ hain hdrop
  obtain ⟨hopen⟩ := IterationProof.internalIteratorDrain v l a x 4 root itag dtag (atag+dropOffset) ptag ctag
    hi hd hdropRoot hpin hcin 4 (.var 0) (.var 1) (.var 2) (.var 3)
  have hclosed : Nonempty (Derivation (S pF pR q) (drainClause pF v l a x bound initial finalizer)) :=
    GorbowTheoryProofProof.monotonicity _ _
      (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) 0 _ ⟨Fuel.Logic.closeAll hopen⟩
  exact ⟨v,l,a,x,bound,initial,finalizer,offset,pF,pR,c,tagCK,pCK,tagG,pG,
    hleaves,hk,hbound,hinitial,hfinal,hoff,hq0,hA,hSyntax,hCK,hInstall,hFixed,
    hG,hGInstall,hkin,hain,hpin,hcin,hstep,hinc,hmono,hfusion,hsuffix,hiterator,
    dropOffset,hdrop,hdropRoot,hd,hclosed⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.SourceProof
