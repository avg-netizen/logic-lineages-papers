module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionEvaluation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation
open GorbowSyntax SixSol20261113
abbrev Installation {n : Nat} (p : GorbowPRProgram.Program n) (old a : GorbowPRProgram.Program 1)
 (x : GorbowPRProgram.Program 3) := RawMulNewestAddCongruences.Installation p old a x
abbrev congruenceCertificate := @RawBinaryAdditionCongruence.certificate
/-- Actual operand-certificate composition followed by the certificate extracted
from the original PR numeral-addition iterator. -/
def certificate {ctx : Nat} (mp leftQ rightQ eqQ ref c a num iter right : Nat)
 (t u m k first second : Term ctx) : Term ctx :=
 RawEqualityComposition.transitivityCertificate mp eqQ ref c a
  (RawAdditionComputation.addRaw c a t u)
  (RawAdditionComputation.addRaw c a (LiteralNumeralPrefix.numeralCall num m) (LiteralNumeralPrefix.numeralCall num k))
  (LiteralNumeralPrefix.numeralCall num (.add m k))
  (RawBinaryAdditionCongruence.certificate mp leftQ rightQ eqQ ref c a
   t (LiteralNumeralPrefix.numeralCall num m) u (LiteralNumeralPrefix.numeralCall num k) first second)
  (RawIteratedSucc.third right (RawNewestAdditionIteration.binaryCall iter k (LiteralNumeralPrefix.numeralCall num m)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation
