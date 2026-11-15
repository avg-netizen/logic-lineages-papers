module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionOutputFrame.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity
open GorbowSyntax SixSol20261113
/-- Original term variable prefix [0,index], with index an arbitrary runtime term. -/
def variableChunk {ctx : Nat} (ctag : Nat) (index : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero (HistoryLookup.consCall ctag index .zero)
def termTasks {ctx : Nat} (ptag ctag : Nat) (depth : Term ctx) : Term ctx :=
 FullFormulaInstantiationValidity.ClosedTermDepthTargets.tasks ptag ctag depth
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity
