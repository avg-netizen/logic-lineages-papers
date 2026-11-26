module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CoreProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralKernelSource.OccurrenceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.InstallationProof
open GorbowPRProgram GorbowPRRegistry GorbowPRChildTags
open SixSol20261112.Fuel LiteralCheckerAuxiliaries

theorem auxiliaries {n : Nat} (p : Program n) (qtag : Nat) (v l a : Program 1) (x : Program 3)
 (hq : (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker v l a x bound initial finalizer⟩) :
 ∃ ptag ctag dtag droptag : Nat,
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ ∧
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ ∧
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ ∧
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ := by
 let k := HistoryKernel.kernel v l a x
 let itag := qtag+LiteralCheckerAcceptance.iteratorOffset v l a x
 let ktag := itag+stepTag SixSol20261112.HistoryMachine.iterationBase+1
 obtain ⟨_,hi⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p qtag v l a x hq
 have hs := Equations.recursionStepChild p itag SixSol20261112.HistoryMachine.iterationBase
  (SixSol20261112.HistoryMachine.iterationStep k) hi
 have hk : (nodes p)[ktag]? = some ⟨3,k⟩ :=
  Equations.functionChild p _ k SixSol20261112.HistoryMachine.iterationArguments hs
 obtain ⟨hp,_,_,_,hc⟩ := HistoryKernel.OptionProof.kernelNodes p ktag v l a x hk
 have hd := HistoryIteratorDrain.InstallationProof.rightInstalled p ktag v l a x hk
 obtain ⟨ao,hao⟩ := LiteralKernelSource.OccurrenceProof.appendOffset v l a x
 have ha := GorbowPRSubtree.Proof.lookupTransport n p ktag ⟨3,k⟩ ao ⟨2,HistoryAppend.append⟩ hk hao
 obtain ⟨dr,hdr⟩ := HistoryIteratorDrain.InstallationProof.dropOffset
 have hdrop := GorbowPRSubtree.Proof.lookupTransport n p (ktag+ao) ⟨2,HistoryAppend.append⟩ dr ⟨2,HistoryLookup.drop⟩ ha hdr
 exact ⟨_,_,_,_,hp,hc,hd,hdrop⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.InstallationProof
