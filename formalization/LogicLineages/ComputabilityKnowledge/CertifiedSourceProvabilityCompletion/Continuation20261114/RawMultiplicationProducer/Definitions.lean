module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Literal original multiplication-right replacement followed by two canonical MPs. -/
def rightCongruence {n : Nat} (t u v cert : Program n) : Program n :=
 let tv := RawMultiplication.Succ.multiplicationRaw t v
 let uv := RawMultiplication.Succ.multiplicationRaw u v
 let result := RawAdditionIteration.eqRaw tv uv
 let self := RawAdditionIteration.eqRaw tv tv
 RawAdditionIteration.mp result
  (RawAdditionIteration.mp (RawSuccReplace.binaryRaw 7 self result)
   (RawAdditionIteration.singleton (RawMulRightReplace.line t u v)) cert)
  (RawAdditionIteration.singleton (applyOne RawReflexivity.lineConstructor tv))
/-- Literal original multiplication-left replacement, unchanged three annotation slots. -/
def leftCongruence {n : Nat} (t u v cert : Program n) : Program n :=
 let vt := RawMultiplication.Succ.multiplicationRaw v t
 let vu := RawMultiplication.Succ.multiplicationRaw v u
 let result := RawAdditionIteration.eqRaw vt vu
 let self := RawAdditionIteration.eqRaw vt vt
 RawAdditionIteration.mp result
  (RawAdditionIteration.mp (RawSuccReplace.binaryRaw 7 self result)
   (RawAdditionIteration.singleton (RawMulLeftReplace.line t u v)) cert)
  (RawAdditionIteration.singleton (applyOne RawReflexivity.lineConstructor vt))
def binaryCongruence {n : Nat} (t t' u u' first second : Program n) : Program n :=
 RawAdditionIteration.transitivity (RawMultiplication.Succ.multiplicationRaw t u)
  (RawMultiplication.Succ.multiplicationRaw t' u) (RawMultiplication.Succ.multiplicationRaw t' u')
  (rightCongruence t t' u first) (leftCongruence u u' t' second)
/-- [raw left,raw right,left value,right value,left certificate,right certificate]. -/
def producer : Program 6 :=
 let t : Program 6 := .projection 0
 let u : Program 6 := .projection 1
 let m : Program 6 := .projection 2
 let k : Program 6 := .projection 3
 let nm := applyOne LiteralNumeralPrefix.numeralCode m
 let nk := applyOne LiteralNumeralPrefix.numeralCode k
 let sum := applyTwo HistoryCodec.multiply k m
 RawAdditionIteration.transitivity (RawMultiplication.Succ.multiplicationRaw t u)
  (RawMultiplication.Succ.multiplicationRaw nm nk) (applyOne LiteralNumeralPrefix.numeralCode sum)
  (binaryCongruence t nm u nk (.projection 4) (.projection 5))
  (RawNewestMultiplicationIteration.thirdRaw (applyTwo RawNewestMultiplicationIteration.iterator k m))
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toAdditionProducer : RawAdditionProducer.Installation p old a x where
 multiplicationProducerTag : Nat
 hmultiplicationProducer : (nodes p)[multiplicationProducerTag]? = some ⟨6,producer⟩
def producerCall {ctx : Nat} (tag : Nat) (t u m k first second : Term ctx) : Term ctx :=
 call tag (t ::ᵥ u ::ᵥ m ::ᵥ k ::ᵥ first ::ᵥ second ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer
