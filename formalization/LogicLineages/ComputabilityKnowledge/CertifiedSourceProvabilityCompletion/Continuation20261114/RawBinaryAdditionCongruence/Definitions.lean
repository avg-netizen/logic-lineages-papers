module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestTransitivity.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryAdditionCongruence
open GorbowSyntax
abbrev Installation {n : Nat} (p : GorbowPRProgram.Program n) (old a : GorbowPRProgram.Program 1) (x : GorbowPRProgram.Program 3) := RawNewestTransitivity.Installation p old a x
/-- Literal certificate: left operand transport, right operand transport, then
original four-MP equality transitivity. No semantic evaluation oracle. -/
def certificate {ctx : Nat} (m leftQ rightQ eqQ ref c a : Nat)
 (t t' u u' first second : Term ctx) : Term ctx :=
 RawEqualityComposition.transitivityCertificate m eqQ ref c a
  (RawAddRightCongruence.addRaw c a t u)
  (RawAddRightCongruence.addRaw c a t' u)
  (RawAddRightCongruence.addRaw c a t' u')
  (RawAddRightCongruence.certificate m rightQ ref c a t t' u first)
  (RawAddLeftCongruence.certificate m leftQ ref c a u u' t' second)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawBinaryAdditionCongruence
