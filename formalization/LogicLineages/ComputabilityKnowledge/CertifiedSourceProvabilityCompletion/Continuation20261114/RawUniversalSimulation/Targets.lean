module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Genuine relational kernel simulation for original and refined literal ASTs.
All successful-output quantifiers are internal. The relation is an induction
invariant, not a premise that any runtime step or run succeeds. -/
def InternalKernelSimulation : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨3,RawUniversalKernelRetention.original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨3,RawUniversalKernelRetention.extended valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (state newState index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (relation ptag state newState)
 (relation ptag (HistoryKernel.kernelCall ot state index fuel)
                (HistoryKernel.kernelCall nt newState index fuel))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalSimulation.Targets
