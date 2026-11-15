module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCoreRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113
abbrev Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) :=
 RawUniversalCongruence.Installation p old a x
/-- The original two-MP syntax certificate, using the literal arithmetic
compiler's certificate CALL, not an assumed proof code. -/
def certificate {k ctx : Nat} (mp q ref c a numeral quote compiled : Nat)
 (t : Term k) (values : List.Vector (Term ctx) k) : Term ctx :=
 RawUniversalCongruence.certificate mp q ref c a (call quote values)
  (LiteralNumeralPrefix.numeralCall numeral (ArithmeticTemplateEvaluation.instantiatedValue t values))
  (call compiled values)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.UniversalArgumentEvaluation
