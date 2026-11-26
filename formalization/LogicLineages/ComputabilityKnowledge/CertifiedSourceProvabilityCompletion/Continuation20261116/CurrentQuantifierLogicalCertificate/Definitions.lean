module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- Actual installed singleton producer call, not an assumed accepted code. -/
def certificate {ctx : Nat} (singletonTag : Nat) (a b : Term ctx) : Term ctx :=
 OriginalQuantifierLogicalProducers.lineCall singletonTag a b
def output {ctx : Nat} (isExists : Bool) (ptag ctag atag : Nat) (a b : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (OriginalQuantifierLogicalProducers.conclusionValue isExists ctag atag a b) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate
