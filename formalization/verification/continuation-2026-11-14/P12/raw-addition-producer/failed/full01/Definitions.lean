module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccessorProducer.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Literal original addition-right replacement followed by two canonical MPs. -/
def rightCongruence {n : Nat} (t u v cert : Program n) : Program n :=
 let tv := RawAddSucc.additionRaw t v
 let uv := RawAddSucc.additionRaw u v
 let result := RawAdditionIteration.eqRaw tv uv
 let self := RawAdditionIteration.eqRaw tv tv
 RawAdditionIteration.mp result
  (RawAdditionIteration.mp (RawSuccReplace.binaryRaw 7 self result)
   (RawAdditionIteration.singleton (RawAddRightReplace.line t u v)) cert)
  (RawAdditionIteration.singleton (applyOne RawReflexivity.lineConstructor tv))
/-- Literal original addition-left replacement, unchanged three annotation slots. -/
def leftCongruence {n : Nat} (t u v cert : Program n) : Program n :=
 let vt := RawAddSucc.additionRaw v t
 let vu := RawAddSucc.additionRaw v u
 let result := RawAdditionIteration.eqRaw vt vu
 let self := RawAdditionIteration.eqRaw vt vt
 RawAdditionIteration.mp result
  (RawAdditionIteration.mp (RawSuccReplace.binaryRaw 7 self result)
   (RawAdditionIteration.singleton (RawAddLeftReplace.line t u v)) cert)
  (RawAdditionIteration.singleton (applyOne RawReflexivity.lineConstructor vt))
def binaryCongruence {n : Nat} (t t' u u' first second : Program n) : Program n :=
 RawAdditionIteration.transitivity (RawAddSucc.additionRaw t u)
  (RawAddSucc.additionRaw t' u) (RawAddSucc.additionRaw t' u')
  (rightCongruence t t' u first) (leftCongruence u u' t' second)
/-- [raw left,raw right,left value,right value,left certificate,right certificate]. -/
def producer : Program 6 :=
 let t : Program 6 := .projection 0
 let u : Program 6 := .projection 1
 let m : Program 6 := .projection 2
 let k : Program 6 := .projection 3
 let nm := applyOne LiteralNumeralPrefix.numeralCode m
 let nk := applyOne LiteralNumeralPrefix.numeralCode k
 let sum := applyTwo HistoryCodec.add k m
 RawAdditionIteration.transitivity (RawAddSucc.additionRaw t u)
  (RawAddSucc.additionRaw nm nk) (applyOne LiteralNumeralPrefix.numeralCode sum)
  (binaryCongruence t nm u nk (.projection 4) (.projection 5))
  (RawNewestMultiplicationIteration.thirdRaw (applyTwo RawAdditionIteration.iterator k nm))
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toEvaluation : RawUnaryEvaluation.Installation p old a x where
 producerTag : Nat
 hproducer : (nodes p)[producerTag]? = some ⟨6,producer⟩
def producerCall {ctx : Nat} (tag : Nat) (t u m k first second : Term ctx) : Term ctx :=
 call tag (t ::ᵥ u ::ᵥ m ::ᵥ k ::ᵥ first ::ᵥ second ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer
