module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxScan.FusionStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport
open GorbowSyntax GorbowPRDefiningEquations SixSol20261113 List.Vector
/-- Original length-driven fold, initial OutputState pair(SOME oldTasks,[]),
then actual original right decoder projection. All arguments are runtime terms. -/
def output {ctx : Nat} (ftag ptag rtag : Nat) (tokens oldTasks raw : Term ctx) : Term ctx :=
 call rtag (UniformClosedSubstitutionRawFold.foldCall ftag tokens
  (HistoryKernel.pairCall ptag (.succ oldTasks) .zero) raw ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport
