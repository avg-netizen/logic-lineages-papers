module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalKernelRetention.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalKernelRetention.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual successful active transition at unchanged history/line/rest and
runtime. Its exact output history is preserved, not merely nonfailure. This
is not yet arbitrary-state or full CODE-bound run simulation. -/
def InternalActiveStep : Prop := ∀ n (p : Program n)
 (valid old arithmetic : Program 1) (x : Program 3) (oldTag newTag ptag ctag : Nat),
 (nodes p)[oldTag]? = some ⟨3,original valid old arithmetic x⟩ →
 (nodes p)[newTag]? = some ⟨3,extended valid old arithmetic x⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (index fuel history line rest output : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (HistoryKernel.kernelCall oldTag
   (HistoryKernel.activeState ptag ctag history line rest) index fuel)
   (HistoryKernel.pairCall ptag (.succ output) rest))
  (.equal (HistoryKernel.kernelCall newTag
   (HistoryKernel.activeState ptag ctag history line rest) index fuel)
   (HistoryKernel.pairCall ptag (.succ output) rest))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalKernelRetention.Targets
