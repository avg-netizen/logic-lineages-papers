module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 SixSol20261112.HistoryMachine
/-- Original PR iterator, arbitrary numeric count and arbitrary encoded input
state. Identical successful output is preserved, with count/index/fuel fixed.
No successful intermediate steps, shape assumption or relational premise. -/
def InternalIteratorRetention : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (ot nt ptag ctag : Nat),
 (nodes p)[ot]? = some ⟨4,original valid old arithmetic x⟩ →
 (nodes p)[nt]? = some ⟨4,extended valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (count state index fuel output rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (iterationCall ot count state index fuel) (HistoryKernel.pairCall ptag (.succ output) rest))
       (.equal (iterationCall nt count state index fuel) (HistoryKernel.pairCall ptag (.succ output) rest))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalIteratorRetention.Targets
