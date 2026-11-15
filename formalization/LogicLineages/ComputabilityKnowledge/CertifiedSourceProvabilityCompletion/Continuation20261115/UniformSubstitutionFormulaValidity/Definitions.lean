module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFoldTransport.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxValidator.FormulaBindingProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity
open GorbowSyntax SixSol20261113
/-- Actual output projection of the original length-driven substitution fold,
starting from SOME[(formula,depth+1)] and empty output. At depth0 this is the
literal original subRaw(1,1,0,[replacement]); no new Program AST is introduced. -/
def substitutedOutput {ctx : Nat} (ftag ptag ctag rtag : Nat)
 (depth tokens replacement : Term ctx) : Term ctx :=
 UniformSubstitutionFoldTransport.output ftag ptag rtag tokens
  (LiteralSyntaxValidator.FormulaBindingProof.taskList ptag ctag (.succ depth)) replacement
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity
