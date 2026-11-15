module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalKernelRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.NoneProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StepGeneralProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention
open GorbowSyntax SixSol20261113
/-- Success-directed same-state simulation, no shape restriction on input. -/
def preserves {ctx : Nat} (ot nt ptag : Nat) (state index fuel output rest : Term ctx) : Formula ctx :=
 .imp (.equal (HistoryKernel.kernelCall ot state index fuel) (HistoryKernel.pairCall ptag (.succ output) rest))
      (.equal (HistoryKernel.kernelCall nt state index fuel) (HistoryKernel.pairCall ptag (.succ output) rest))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalStateRetention
