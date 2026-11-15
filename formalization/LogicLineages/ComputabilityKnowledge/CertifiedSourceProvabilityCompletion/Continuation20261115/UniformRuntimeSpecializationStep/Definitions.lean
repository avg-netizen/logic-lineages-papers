module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep
open GorbowSyntax SixSol20261113
/-- Actual dynamic substituted body, retaining the original environment codec. -/
def body {n inputs ctx : Nat} (ctag atag : Nat)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (raw : List.Vector (Term ctx) inputs) (replacement : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.formulaValue ctag atag (List.Vector.cons replacement raw) f
  (UniformRuntimeEnvironmentAgreement.specialize e)
/-- Original numeric MP constructor: implication certificate first, arbitrary
accepted antecedent certificate second, then the actual numeric MP line. -/
def certificate {n inputs ctx : Nat} (mtag ctag atag constructorTag : Nat)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (raw : List.Vector (Term ctx) inputs) (replacement antecedent : Term ctx) : Term ctx :=
 LiteralMPRun.certificate mtag .zero (body ctag atag e f raw replacement)
  (UniformClosedRule13Certificate.certificate ctag constructorTag
   (FixedFormulaSubstitution.formulaValue ctag atag raw f e) replacement) antecedent
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep
