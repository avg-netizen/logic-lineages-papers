module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CoreProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112 LiteralCheckerAuxiliaries

theorem sameSourceCoreAcceptance : Targets.SameSourceCoreAcceptance := by
  obtain ⟨v,l,a,x,offset,pF,pR,c,tagCK,pCK,tagG,pG,
    hleaves,hk,hcal,hbound,hinitial,hfinal,hoff,hq0,hA,hSyntax,hCK,hInstall,hFixed,
    hG,hGInstall,hkin,hain,hpin,hcin,hstep,hinc,hmono,hfusion,hsuffix,hiterator,
    dropOffset,hdrop,hdropRoot,hright,hdrain,hboundNode,hinitialNode,hfinalNode,
    hboundEq,hinitialEq,hfinishEq,hfailureEq⟩ := LiteralCheckerAuxiliaries.SourceProof.sameSourceLiteralAuxiliaries
  let q0 := LiteralKernelSource.coreChecker v l a x bound initial finalizer
  let q := LiteralKernelSource.verifier v l a x bound initial finalizer
  let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
  let fuelTag := GorbowNamedInternalProvability.checkerTag pF
  let ptag := LiteralKernelSource.pairTag pF v l a x bound initial finalizer
  let ctag := LiteralKernelSource.consTag pF v l a x bound initial finalizer
  let atag := LiteralKernelSource.appendTag pF v l a x bound initial finalizer offset
  let dtag := HistoryIteratorDrain.rightTag pF v l a x bound initial finalizer
  have ht : (nodes root)[fuelTag]? = some ⟨5,q⟩ := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR q
  have hcore := LiteralCheckerAuxiliaries.InstallationProof.coreInstalled root fuelTag q0 ht
  obtain ⟨hopen⟩ := CoreProof.internalCoreAcceptance 4 root (coreTag pF v l a x) ptag ctag dtag (atag+dropOffset)
    v l a x hcore hpin hcin hright hdropRoot 5 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
  have hclosedBase : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory root) (acceptanceClause pF v l a x)) := by
    simpa only [acceptanceClause,loopTag,iteratorOffset,Nat.add_assoc,ptag,ctag] using
      (show Nonempty (Derivation (GorbowPRNumeralCalculation.Theory root) _) from ⟨Fuel.Logic.closeAll hopen⟩)
  have hclosed : Nonempty (Derivation (S pF pR q) (acceptanceClause pF v l a x)) :=
    GorbowTheoryProofProof.monotonicity (GorbowPRNumeralCalculation.Theory root) (S pF pR q)
      (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) 0 _ hclosedBase
  exact ⟨v,l,a,x,offset,pF,pR,c,tagCK,pCK,tagG,pG,
    hleaves,hk,hcal,hbound,hinitial,hfinal,hoff,hq0,hA,hSyntax,hCK,hInstall,hFixed,
    hG,hGInstall,hkin,hain,hpin,hcin,hstep,hinc,hmono,hfusion,hsuffix,hiterator,
    dropOffset,hdrop,hdropRoot,hright,hdrain,hboundNode,hinitialNode,hfinalNode,
    hboundEq,hinitialEq,hfinishEq,hfailureEq,hclosed⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.SourceProof
