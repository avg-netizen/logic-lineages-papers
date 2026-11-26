module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.Proof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open RawUniversalCoreRetention.WitnessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LiteralCheckerAcceptance

theorem internalCoreRetention : Targets.InternalCoreRetention := by
 intro template n p v l a x ot nt ptag ctag rightTag dropTag ho hn hp hc hd hdrop ctx index fuel context formula code
 obtain ⟨_,hio⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p ot v l a x ho
 obtain ⟨_,hin⟩ := LiteralCheckerAcceptance.CoreProof.coreNodes p nt v (FullFormulaInstantiation.logicalLeaf template l) a x hn
 obtain ⟨hao⟩ := LiteralCheckerAcceptance.CoreProof.internalCoreAcceptance n p ot ptag ctag rightTag dropTag v l a x ho hp hc hd hdrop ctx index fuel context formula code
 obtain ⟨han⟩ := LiteralCheckerAcceptance.CoreProof.internalCoreAcceptance n p nt ptag ctag rightTag dropTag v (FullFormulaInstantiation.logicalLeaf template l) a x hn hp hc hd hdrop ctx index fuel context formula code
 obtain ⟨hw⟩ := WitnessProof.witnessRetention template p v l a x
  (ot+iteratorOffset v l a x) (nt+iteratorOffset v (FullFormulaInstantiation.logicalLeaf template l) a x) ptag ctag hio hin hp hc index fuel context formula code
 simp only [acceptance,LiteralCheckerAcceptance.WitnessProof.frozenWitness] at hao han
 have forward := Derivation.mp (.logical (.andLeft _ _)) hao
 have backward := Derivation.mp (.logical (.andRight _ _)) han
 exact ⟨Hilbert.compose backward (Hilbert.compose hw forward)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.Proof.internalCoreRetention
