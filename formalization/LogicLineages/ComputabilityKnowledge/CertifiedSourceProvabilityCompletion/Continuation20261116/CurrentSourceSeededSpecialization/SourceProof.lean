module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Literal current tags, not a newly selected registry or checker. -/
def finiteInstallation {arity k : Nat} (p : Program arity) (f : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 FiniteRuleFourCertificate.Installation p (CumulativeUniformRule12Source.logical f lhs rhs old)
  (CumulativeUniformRule12Source.arithmetic a) baseX :=
 ⟨I.current.ptag,I.current.ctag,I.current.iteratorTag,I.current.coreTag,I.current.verifierTag,
  I.current.h_ptag,I.current.h_ctag,I.current.h_iterator,I.current.h_core,I.current.h_verifier⟩
theorem inclusion (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) :
 ∀ sigma, GorbowPRNumeralCalculation.Theory
  (CumulativeUniformRule12Source.root f lhs rhs pF pR old a baseX) sigma →
 S pF pR (CumulativeUniformRule12Source.verifier f lhs rhs old a baseX) sigma := by
 intro sigma h
 exact List.mem_append_left _ (List.mem_append_left _ h)
theorem exactTrace : Targets.InternalSeededTrace := by
 intro installed lhs rhs k t old a baseX pF pR c hA I n f sigma ctx
 have h := PrescribedRuntimeSpecialization.StatementChecks.exactPrescribedTrace
  4 (CumulativeUniformRule12Source.root installed lhs rhs pF pR old a baseX)
  (CumulativeUniformRule12Registry.previousLogical installed lhs rhs old)
  (Continuation20261114.RawMulNewestAddition.arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  I.previous.current I.previous.previous.previous.previous.mpTag
  I.previous.previous.previous.previous.hmp n f sigma ctx (PrescribedSourceAxiomSpecialization.seed f)
 exact GorbowTheoryProofProof.monotonicity _ _
  (inclusion installed lhs rhs pF pR old a baseX) ctx _ h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.SourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.SourceProof
