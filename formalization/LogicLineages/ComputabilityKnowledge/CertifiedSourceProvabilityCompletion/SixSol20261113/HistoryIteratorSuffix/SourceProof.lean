module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.IterationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112

/-- Reuse precisely the accepted literal-source witnesses. Nothing is reselected,
reinstalled, padded, or identified with the earlier opaque kernel. -/
theorem sameSourceIteratorSuffix : Targets.SameSourceIteratorSuffix := by
  obtain ⟨v,l,a,x,bound,initial,finalizer,offset,pF,pR,c,tagCK,pCK,tagG,pG,
    hleaves,hk,hbound,hinitial,hfinal,hoff,hq0,hA,hSyntax,hCK,hInstall,hFixed,
    hG,hGInstall,hkin,hain,hpin,hcin,hstep,hinc,hmono,hfusion,hsuffix⟩ :=
    LiteralKernelSource.SourceProof.sameSourceLiteralKernel
  let k := HistoryKernel.kernel v l a x
  let q := LiteralKernelSource.verifier v l a x bound initial finalizer
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let fuelTag := GorbowNamedInternalProvability.checkerTag pF
  let itag := SixSol20261112.HistoryMachine.iteratorTag fuelTag k bound initial finalizer
  let atag := LiteralKernelSource.appendTag pF v l a x bound initial finalizer offset
  let ptag := LiteralKernelSource.pairTag pF v l a x bound initial finalizer
  let ctag := LiteralKernelSource.consTag pF v l a x bound initial finalizer
  have ht : (nodes root)[fuelTag]? = some ⟨5,q⟩ :=
    GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  have hi := SixSol20261113.HistoryMachine.SourceProof.iteratorInstalled root fuelTag k bound initial finalizer ht
  obtain ⟨hd⟩ := IterationProof.internalIteratorSuffix v l a x 4 root itag atag ptag ctag hi hain hpin hcin 8
    (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6) (.var 7)
  have hclosed : Nonempty (Derivation (S pF pR q)
      (iteratorClause pF v l a x bound initial finalizer offset)) :=
    GorbowTheoryProofProof.monotonicity _ _
      (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) 0 _ ⟨Fuel.Logic.closeAll hd⟩
  exact ⟨v,l,a,x,bound,initial,finalizer,offset,pF,pR,c,tagCK,pCK,tagG,pG,
    hleaves,hk,hbound,hinitial,hfinal,hoff,hq0,hA,hSyntax,hCK,hInstall,hFixed,
    hG,hGInstall,hkin,hain,hpin,hcin,hstep,hinc,hmono,hfusion,hsuffix,hclosed⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SourceProof
