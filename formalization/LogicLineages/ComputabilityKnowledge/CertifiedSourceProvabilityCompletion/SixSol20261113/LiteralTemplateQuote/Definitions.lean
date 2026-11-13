module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitution
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector HistoryRuleSuffix
/-- Prefix a literal ORIGINAL term token to an encoded child stream. -/
def prependToken {k : Nat} (token : Nat) (child : Program k) : Program k :=
 applyTwo HistoryCodec.cons (constant k token) child
/-- Syntax quotation after replacing each free variable by its runtime numeral.
This is NOT evaluation: universalFunction contributes token5 and is not run.
The template is external finite syntax; any future checker tag can be supplied
as a runtime variable, so this construction does not choose a circular pF. -/
def templateQuote {k : Nat} : Term k → Program k
 | .var i => applyOne LiteralNumeralPrefix.numeralCode (.projection i)
 | .zero => prependToken 1 (constant k 0)
 | .succ t => prependToken 2 (templateQuote t)
 | .add t u => prependToken 3 (applyTwo HistoryAppend.append (templateQuote t) (templateQuote u))
 | .mul t u => prependToken 4 (applyTwo HistoryAppend.append (templateQuote t) (templateQuote u))
 | .universalFunction t => prependToken 5 (templateQuote t)
def quoteCall {k ctx : Nat} (tag : Nat) (values : List.Vector (Term ctx) k) : Term ctx :=
 call tag values
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralTemplateQuote
