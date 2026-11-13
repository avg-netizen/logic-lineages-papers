module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel
open GorbowSyntax SixSol20261112.Fuel HistoryKernel
/-- Only an actual successful step is transported, retaining the exact
output history and remainder. Rejection at low fuel need not remain rejection. -/
def stepTransport {ctx : Nat} (ktag ptag : Nat)
 (index s t h lines out rest : Term ctx) : Formula ctx :=
 .imp (orderGuard s t)
  (.imp (.equal (kernelCall ktag (pairCall ptag (.succ h) lines) index s)
    (pairCall ptag (.succ out) rest))
   (.equal (kernelCall ktag (pairCall ptag (.succ h) lines) index t)
    (pairCall ptag (.succ out) rest)))
/-- Original runtime count, raw lines and SAME final positive option. There
is no numeral enumeration, decoded-list or intermediate-success premise. -/
def iteratorTransport {ctx : Nat} (itag ptag : Nat)
 (count index s t h lines out rest : Term ctx) : Formula ctx :=
 .imp (orderGuard s t)
  (.imp (.equal (SixSol20261112.HistoryMachine.iterationCall itag count
    (pairCall ptag (.succ h) lines) index s) (pairCall ptag (.succ out) rest))
   (.equal (SixSol20261112.HistoryMachine.iterationCall itag count
    (pairCall ptag (.succ h) lines) index t) (pairCall ptag (.succ out) rest)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel
