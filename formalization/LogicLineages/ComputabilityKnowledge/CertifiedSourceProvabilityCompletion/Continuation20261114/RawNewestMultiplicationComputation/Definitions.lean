module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccIteration.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toEvaluator : RawMulNewestAdditionIteration.Installation p old a x where
 mulZeroTag : Nat
 mulSuccTag : Nat
 congruenceStepTag : Nat
 congruenceIteratorTag : Nat
 hmulZero : (nodes p)[mulZeroTag]? = some ⟨1,RawMultiplication.Zero.lineConstructor⟩
 hmulSucc : (nodes p)[mulSuccTag]? = some ⟨2,RawMultiplication.Succ.lineConstructor⟩
 hcongruenceStep : (nodes p)[congruenceStepTag]? = some ⟨1,RawMulNewestSuccIteration.step⟩
 hcongruenceIterator : (nodes p)[congruenceIteratorTag]? = some ⟨2,RawMulNewestSuccIteration.iterator⟩
def mulRaw {ctx : Nat} (c a : Nat) (t u : Term ctx) : Term ctx :=
 HistoryLookup.consCall c (Term.numeral 4) (HistoryAppend.appendCall a t u)
def stepCertificate {ctx : Nat}
 (mp right ref mulSucc addIterator congruenceIterator num pref p c a r : Nat)
 (m u z cert : Term ctx) : Term ctx :=
 let t := LiteralNumeralPrefix.numeralCall num m
 let v := LiteralNumeralPrefix.numeralCall num z
 let product := mulRaw c a t u
 let answer := LiteralNumeralPrefix.numeralCall num (.add z m)
 RawEqualityComposition.transitivityCertificate mp right ref c a
  (mulRaw c a t (RawAdditionComputation.succRaw c u))
  (RawAdditionComputation.addRaw c a product t) answer
  (RawMultiplicationCertificates.SuccCertificate.certificate c mulSucc t u)
  (RawEqualityComposition.transitivityCertificate mp right ref c a
   (RawAdditionComputation.addRaw c a product t)
   (RawAdditionIteration.binaryCall pref m product) answer
   (RawIteratedSucc.third r (RawAdditionIteration.binaryCall addIterator m product))
   (RawIteratedSucc.third r (RawIteratedSucc.iteratorCall congruenceIterator m
    (RawIteratedSucc.state p product v cert))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation
