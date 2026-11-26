module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Proof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalCoreRetention.WitnessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LiteralCheckerAcceptance

theorem internalCoreRetention : Targets.InternalCoreRetention := by
 intro n p v l a x ot nt ptag ctag rightTag dropTag ho hn hp hc hd hdrop ctx index fuel context formula code
 obtain ⟨_,hio⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p ot v l a x ho
 obtain ⟨_,hin⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p nt v (UniformClosedRule13.logicalLeaf l) a x hn
 obtain ⟨hao⟩ := LiteralCheckerAcceptance.CoreProof.internalCoreAcceptance n p ot ptag ctag rightTag dropTag v l a x ho hp hc hd hdrop ctx index fuel context formula code
 obtain ⟨han⟩ := LiteralCheckerAcceptance.CoreProof.internalCoreAcceptance n p nt ptag ctag rightTag dropTag v (UniformClosedRule13.logicalLeaf l) a x hn hp hc hd hdrop ctx index fuel context formula code
 obtain ⟨hw⟩ := WitnessProof.witnessRetention p v l a x
  (ot+iteratorOffset v l a x) (nt+iteratorOffset v (UniformClosedRule13.logicalLeaf l) a x) ptag ctag hio hin hp hc index fuel context formula code
 simp only [acceptance,LiteralCheckerAcceptance.WitnessProof.frozenWitness] at hao han
 have forward := Derivation.mp (.logical (.andLeft _ _)) hao
 have backward := Derivation.mp (.logical (.andRight _ _)) han
 exact ⟨Hilbert.compose backward (Hilbert.compose hw forward)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention.Proof.internalCoreRetention
