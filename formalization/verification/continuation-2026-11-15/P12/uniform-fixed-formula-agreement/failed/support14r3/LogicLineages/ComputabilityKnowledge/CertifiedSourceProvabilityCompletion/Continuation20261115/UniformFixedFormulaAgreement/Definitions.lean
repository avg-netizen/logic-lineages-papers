module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement
open GorbowSyntax
/-- Exact original uniform output on the literal unary template code. -/
def uniformValue {ctx : Nat} (ftag ptag ctag rtag : Nat)
 (f : Formula 1) (replacement : Term ctx) : Term ctx :=
 UniformSubstitutionFormulaValidity.substitutedOutput ftag ptag ctag rtag .zero
  (Term.numeral (FullFormulaInstantiation.templateCode f)) replacement
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement
