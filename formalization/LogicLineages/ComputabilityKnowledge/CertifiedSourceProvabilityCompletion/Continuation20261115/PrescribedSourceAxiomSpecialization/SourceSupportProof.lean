module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SourceSupportProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Reuse the same actual tags, with no tuple or registry reconstruction. -/
def finiteInstallation {arity : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic (SaturatedAxiomLeaf.saturated x)) :
 FiniteRuleFourCertificate.Installation p (UniformClosedRule13.logicalLeaf old) arithmetic x :=
 ⟨I.ptag,I.ctag,I.iteratorTag,I.coreTag,I.verifierTag,I.h_ptag,I.h_ctag,I.h_iterator,I.h_core,I.h_verifier⟩
theorem inclusion (pF pR old arithmetic : Program 1) (x : Program 3) :
 ∀ sigma, GorbowPRNumeralCalculation.Theory (root pF pR old arithmetic x) sigma →
 S pF pR (verifier old arithmetic x) sigma := by
 intro sigma h
 exact List.mem_append_left _ (List.mem_append_left _ h)
/-- Source-theory lifting plus actual local-hypothesis substitution. This does
not regard a source-local guard as an axiom of the smaller registry theory. -/
theorem localCut {T U : Sentence → Prop} {ctx : Nat} {Gamma G : List (Formula ctx)} {phi : Formula ctx}
 (hTU : ∀ sigma, T sigma → U sigma)
 (hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi))
 (h : Nonempty (Hilbert.Local T ctx Gamma phi)) : Nonempty (Hilbert.Local U ctx G phi) := by
 obtain ⟨h⟩ := h
 induction h with
 | base d =>
  obtain ⟨hd⟩ := GorbowTheoryProofProof.monotonicity T U hTU ctx _ ⟨d⟩
  exact ⟨.base hd⟩
 | hypothesis h => exact hG _ h
 | mp a b iha ihb =>
  obtain ⟨ha⟩ := iha
  obtain ⟨hb⟩ := ihb
  exact ⟨.mp ha hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SourceSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SourceSupportProof
