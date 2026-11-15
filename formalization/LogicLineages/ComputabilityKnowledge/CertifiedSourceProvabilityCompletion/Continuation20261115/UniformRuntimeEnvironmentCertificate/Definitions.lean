module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentAgreement.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Certificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate
open GorbowSyntax SixSol20261113
/-- Exact original universal-instantiation conclusion on a dynamic runtime
formula code. Its substituted consequent is not treated as a fixed template. -/
def conclusion {n inputs ctx : Nat} (ctag atag : Nat)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (raw : List.Vector (Term ctx) inputs) (replacement : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.binaryValue ctag atag 7
  (FixedFormulaSubstitution.unaryValue ctag 10 (FixedFormulaSubstitution.formulaValue ctag atag raw f e))
  (FixedFormulaSubstitution.formulaValue ctag atag (List.Vector.cons replacement raw) f
   (UniformRuntimeEnvironmentAgreement.specialize e))
/-- Same successful original singleton output, using the identified conclusion. -/
def output {ctx : Nat} (ptag ctag : Nat) (F : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero F .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate
