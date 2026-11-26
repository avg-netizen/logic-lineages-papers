module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- One actual newest checker with both original addition arithmetic clauses. -/
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toCongruence : RawRetainedSuccCongruence.Installation p old (RawCumulativeArithmetic.arithmetic a) x where
 zeroTag : Nat
 addTag : Nat
 arithmeticTag : Nat
 hzero : (nodes p)[zeroTag]? = some ⟨1,RawAddZero.lineConstructor⟩
 hadd : (nodes p)[addTag]? = some ⟨2,RawAddSucc.lineConstructor⟩
 harithmetic : (nodes p)[arithmeticTag]? = some ⟨1,RawCumulativeArithmetic.arithmetic a⟩
def zeroRaw {ctx : Nat} (c : Nat) : Term ctx := HistoryLookup.consCall c (.succ .zero) .zero
def addRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx :=
 HistoryLookup.consCall c (Term.numeral 3) (HistoryAppend.appendCall a t u)
def succRaw {ctx : Nat} (c : Nat) (t : Term ctx) : Term ctx := RawSuccReplace.succValue c t
/-- Real addition recursion certificate: original addSucc axiom, successor
congruence of input computation, then original equality transitivity. -/
def stepCertificate {ctx : Nat} (m right replace ref add c a : Nat) (t u v cert : Term ctx) : Term ctx :=
 RawEqualityComposition.transitivityCertificate m right ref c a
  (addRaw c a t (succRaw c u)) (succRaw c (addRaw c a t u)) (succRaw c v)
  (RawAddSuccCertificate.certificate c add t u)
  (RawSuccCongruence.certificate m replace ref c a (addRaw c a t u) v cert)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation
