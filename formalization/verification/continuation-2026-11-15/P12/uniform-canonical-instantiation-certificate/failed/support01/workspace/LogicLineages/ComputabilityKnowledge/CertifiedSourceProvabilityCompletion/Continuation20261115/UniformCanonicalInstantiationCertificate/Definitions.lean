module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Certificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate
open GorbowSyntax SixSol20261113
/-- Original successful singleton state, with the capture-correct original
instantiation conclusion rather than an unidentified runtime case13 output. -/
def canonicalOutput {ctx : Nat} (ptag ctag atag : Nat) (f : Formula 1) (raw : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (FullFormulaInstantiation.formulaValue ctag atag f raw) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate
