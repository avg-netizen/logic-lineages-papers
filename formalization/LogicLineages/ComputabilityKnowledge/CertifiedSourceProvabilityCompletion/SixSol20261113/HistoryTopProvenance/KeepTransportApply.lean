module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransportApply
open GorbowSyntax GorbowTheoryProof KeepSyntax
noncomputable def lines {T : Sentence → Prop} {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
 (option a b context raw tail remaining index fuel : Term ctx)
 (he : Derivation T (.equal a b))
 (h : Derivation T (stateKeep itag ptag ctag vtag leftTag rightTag option a context raw tail remaining index fuel)) :
 Derivation T (stateKeep itag ptag ctag vtag leftTag rightTag option b context raw tail remaining index fuel) :=
 .mp (.mp (KeepTransport.lines itag ptag ctag vtag leftTag rightTag option a b context raw tail remaining index fuel) he) h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.KeepTransportApply
