module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryMultiplicationCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation
open GorbowSyntax SixSol20261113
abbrev Installation {n : Nat} (p : GorbowPRProgram.Program n) (old a : GorbowPRProgram.Program 1)
 (x : GorbowPRProgram.Program 3) := RawNewestMultiplicationIteration.Installation p old a x
/-- Actual operand-certificate composition followed by the certificate extracted
from the original PR numeral-multiplication iterator. -/
def certificate {ctx : Nat} (mp leftQ rightQ eqQ ref c a num iter right : Nat)
 (t u m k first second : Term ctx) : Term ctx :=
 RawEqualityComposition.transitivityCertificate mp eqQ ref c a
  (RawNewestMultiplicationComputation.mulRaw c a t u)
  (RawNewestMultiplicationComputation.mulRaw c a (LiteralNumeralPrefix.numeralCall num m) (LiteralNumeralPrefix.numeralCall num k))
  (LiteralNumeralPrefix.numeralCall num (.mul m k))
  (RawBinaryMultiplicationCongruence.certificate mp leftQ rightQ eqQ ref c a
   t (LiteralNumeralPrefix.numeralCall num m) u (LiteralNumeralPrefix.numeralCall num k) first second)
  (RawIteratedSucc.third right (RawAdditionIteration.binaryCall iter k m))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation
