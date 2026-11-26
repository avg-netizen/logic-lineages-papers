module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
def thirdRaw {n : Nat} (q : Program n) : Program n :=
 applyOne (HistoryDecoder.decoder true) (applyOne (HistoryDecoder.decoder true) q)
/-- HistoryCodec.add evaluates its arguments [m,z] as z+m. -/
def nextValue {n : Nat} (m z : Program n) : Program n := applyTwo HistoryCodec.add m z
def computation {n : Nat} (m u z cert : Program n) : Program n :=
 let t := applyOne LiteralNumeralPrefix.numeralCode m
 let v := applyOne LiteralNumeralPrefix.numeralCode z
 let product := RawMultiplication.Succ.multiplicationRaw t u
 let answer := applyOne LiteralNumeralPrefix.numeralCode (nextValue m z)
 RawAdditionIteration.transitivity
  (RawMultiplication.Succ.multiplicationRaw t (RawAddSucc.successorRaw u))
  (RawAddSucc.additionRaw product t) answer
  (RawAdditionIteration.singleton (RawMultiplication.Succ.line t u))
  (RawAdditionIteration.transitivity (RawAddSucc.additionRaw product t)
   (applyTwo RawAdditionIteration.successorPrefix m product) answer
   (thirdRaw (applyTwo RawAdditionIteration.iterator m product))
   (thirdRaw (applyTwo RawIteratedSucc.iterator m (RawAdditionIteration.stateRaw product v cert))))
def base : Program 1 := RawAdditionIteration.stateRaw
 (applyTwo HistoryCodec.cons (constant 1 1) (constant 1 0)) (constant 1 0)
 (RawAdditionIteration.singleton (applyOne RawMultiplication.Zero.lineConstructor
  (applyOne LiteralNumeralPrefix.numeralCode (.projection 0))))
def rightRaw : Program 2 := applyOne (HistoryDecoder.decoder false) (.projection 1)
def value : Program 2 := applyOne (HistoryDecoder.decoder false)
 (applyOne (HistoryDecoder.decoder true) (.projection 1))
def certificateRaw : Program 2 := thirdRaw (.projection 1)
/-- Inputs [fixed numeral value m, state(rightRaw,numericValue,certificate)]. -/
def step : Program 2 := RawAdditionIteration.stateRaw (RawAddSucc.successorRaw rightRaw)
 (nextValue (.projection 0) value) (computation (.projection 0) rightRaw value certificateRaw)
def iterator : Program 2 := .recursion base (applyTwo step (.projection 2) (.projection 1))
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 toComputation : RawNewestMultiplicationComputation.Installation p old a x where
 numericAddTag : Nat
 mulBaseTag : Nat
 mulStepTag : Nat
 mulIteratorTag : Nat
 hnumericAdd : (nodes p)[numericAddTag]? = some ⟨2,HistoryCodec.add⟩
 hmulBase : (nodes p)[mulBaseTag]? = some ⟨1,base⟩
 hmulStep : (nodes p)[mulStepTag]? = some ⟨2,step⟩
 hmulIterator : (nodes p)[mulIteratorTag]? = some ⟨2,iterator⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration
