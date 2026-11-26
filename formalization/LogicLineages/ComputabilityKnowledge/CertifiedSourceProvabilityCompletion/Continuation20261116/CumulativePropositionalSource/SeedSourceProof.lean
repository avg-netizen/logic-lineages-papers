module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CapabilitySupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
def finiteInstallation {arity k : Nat} (p : Program arity) (f : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (I : JointInstallation p f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 FiniteRuleFourCertificate.Installation p (logical f lhs rhs old) (arithmetic a) baseX :=
 ⟨I.currentK.ptag,I.currentK.ctag,I.currentK.iteratorTag,I.currentK.coreTag,I.currentK.verifierTag,
  I.currentK.h_ptag,I.currentK.h_ctag,I.currentK.h_iteratorTag,I.currentK.h_coreTag,I.currentK.h_verifierTag⟩
theorem inclusion (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) :
 ∀ sigma, GorbowPRNumeralCalculation.Theory (root f lhs rhs pF pR old a baseX) sigma →
 S pF pR (verifier f lhs rhs old a baseX) sigma := by
 intro sigma h
 exact List.mem_append_left _ (List.mem_append_left _ h)
theorem priorRetentionInternal {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x)
 (index fuel context formula code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.previous.current.coreTag index fuel context formula code) (.succ .zero))
   (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel context formula code) (.succ .zero)))) := by
 obtain ⟨hp⟩ := CumulativeUniformRule12Registry.CapabilityProof.retention p f lhs rhs t old a x I.previous ctx index fuel context formula code
 obtain ⟨hn⟩ := CapabilitySupport.retentionInternal p f lhs rhs t old a x I index fuel context formula code
 exact ⟨Hilbert.compose hn hp⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedSourceProof
