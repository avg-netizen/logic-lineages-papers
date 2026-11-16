module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- Exact unary PR call in the literal source language. -/
def unary : Term 1 := call GorbowSourceRegistryPadding.functionTag (.var 0 ::ᵥ nil)
def header : Term 2 := CurrentNamedHeaderCertificate.template
def value : Program 2 := ArithmeticTemplateEvaluation.valueProgram header
def headerQuote : Program 2 := LiteralTemplateQuote.templateQuote header
def numberQuote : Program 2 := HistoryRuleSuffix.applyOne LiteralNumeralPrefix.numeralCode value
def leftQuote : Program 2 := LiteralTemplateQuote.templateQuote (.universalFunction header)
def middleQuote : Program 2 := LiteralTemplateQuote.templateQuote (call GorbowSourceRegistryPadding.functionTag (header ::ᵥ nil))
def rightQuote : Program 2 := .composition (LiteralTemplateQuote.templateQuote unary) (fun _ => value)
/-- The ordinary unary recipe consumes the actual arithmetic header certificate. -/
def congruence : Program 2 := CurrentCallCongruenceProgram.unaryClosed unary headerQuote numberQuote
 (ArithmeticTemplateEvaluation.certificateProgram header)
/-- Original transitivity order: named alias, then PR-call header reduction.
No computation of pF is claimed by this packet. -/
def program : Program 2 := CurrentRecursionBaseProgram.transitivity leftQuote middleQuote rightQuote
 CurrentNamedAliasCertificate.program congruence
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨6,CurrentNamedHeaderCertificate.extra f lhs rhs t rawOld ar baseX⟩,⟨2,program⟩]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport
