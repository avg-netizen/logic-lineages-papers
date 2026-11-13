module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepSyntax
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepApplication
open GorbowSyntax GorbowTheoryProof KeepSyntax
noncomputable def apply {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 (itag ptag ctag vtag leftTag rightTag : Nat)
 (code context raw tail remaining index fuel : Term ctx)
 (hk : Derivation T (keep itag ptag ctag vtag leftTag rightTag code context raw tail remaining index fuel))
 (ih : Hilbert.Local T ctx G (.imp (.equal code
   (HistoryRunSplice.state ptag (.succ (HistoryLookup.consCall ctag
     (HistoryKernel.pairCall ptag context raw) tail)) remaining))
   (topWitness vtag leftTag rightTag context raw)))
 (he : Hilbert.Local T ctx G (.equal (HistoryKernel.kernelCall (kernelTag itag) code index fuel)
   (HistoryRunSplice.state ptag (.succ (HistoryLookup.consCall ctag
     (HistoryKernel.pairCall ptag context raw) tail)) remaining))) :
 Hilbert.Local T ctx G (topWitness vtag leftTag rightTag context raw) := by
 have h := hk
 unfold keep at h
 exact .mp (.mp (.base h) ih) he
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepApplication
