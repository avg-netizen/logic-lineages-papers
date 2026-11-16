module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The exact original two-argument named header, with both runtime variables. -/
def template : Term 2 := GorbowNamedDefiningTheory.headerVariables (2,0)
/-- Install the literal arithmetic compiler triple before choosing a source. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨6,CurrentNamedAliasCertificate.extra f lhs rhs t rawOld ar baseX⟩,
  ⟨2,LiteralTemplateQuote.templateQuote template⟩,
  ⟨2,ArithmeticTemplateEvaluation.valueProgram template⟩,
  ⟨2,ArithmeticTemplateEvaluation.certificateProgram template⟩]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate
