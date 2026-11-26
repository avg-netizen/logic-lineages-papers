module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransportApply
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepStateCode
open GorbowSyntax GorbowTheoryProof KeepSyntax
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option lines code context raw tail remaining index fuel : Term ctx)
 (he : Derivation T (.equal (HistoryRunSplice.state ptag option lines) code))
 (h : Derivation T (stateKeep itag ptag ctag vtag leftTag rightTag option lines context raw tail remaining index fuel)) :
 Derivation T (keep itag ptag ctag vtag leftTag rightTag code context raw tail remaining index fuel) := by
 have h' : Derivation T (keep itag ptag ctag vtag leftTag rightTag
   (HistoryRunSplice.state ptag option lines) context raw tail remaining index fuel) := by
   simpa only [stateKeep] using h
 exact .mp (.mp (KeepSyntax.transport itag ptag ctag vtag leftTag rightTag
   (HistoryRunSplice.state ptag option lines) code context raw tail remaining index fuel) he) h'
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepStateCode
