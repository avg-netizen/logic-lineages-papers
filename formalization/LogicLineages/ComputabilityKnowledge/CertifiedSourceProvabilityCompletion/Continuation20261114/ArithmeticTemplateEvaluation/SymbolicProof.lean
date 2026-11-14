module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.ValueStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

def raw {k ctx : Nat} (num c a : Nat) (values : List.Vector (Term ctx) k) : Term k → Term ctx
 | .var i => LiteralNumeralPrefix.numeralCall num (values.get i)
 | .zero => RawAdditionComputation.zeroRaw c
 | .succ t => RawAdditionComputation.succRaw c (raw num c a values t)
 | .add t u => RawAdditionComputation.addRaw c a (raw num c a values t) (raw num c a values u)
 | .mul t u => RawNewestMultiplicationComputation.mulRaw c a (raw num c a values t) (raw num c a values u)
 | .universalFunction _ => .zero

def certificate {n k ctx : Nat} {p : Program n} {old a : Program 1} {x : Program 3}
 (I : Installation p old a x) (values : List.Vector (Term ctx) k) : Term k → Term ctx
 | .var i => RawCumulativeLogical.certificate I.consTag I.reflexivityTag (raw I.numeralTag I.consTag I.appendTag values (.var i))
 | .zero => RawCumulativeLogical.certificate I.consTag I.reflexivityTag (RawAdditionComputation.zeroRaw I.consTag)
 | .succ t => RawSuccessorProducer.producerCall I.successorProducerTag
   (raw I.numeralTag I.consTag I.appendTag values t) (instantiatedValue t values) (certificate I values t)
 | .add t u => RawAdditionProducer.producerCall I.producerTag
   (raw I.numeralTag I.consTag I.appendTag values t) (raw I.numeralTag I.consTag I.appendTag values u)
   (instantiatedValue t values) (instantiatedValue u values) (certificate I values t) (certificate I values u)
 | .mul t u => RawMultiplicationProducer.producerCall I.multiplicationProducerTag
   (raw I.numeralTag I.consTag I.appendTag values t) (raw I.numeralTag I.consTag I.appendTag values u)
   (instantiatedValue t values) (instantiatedValue u values) (certificate I values t) (certificate I values u)
 | .universalFunction _ => .zero

theorem quoteComputes {k : Nat} (t : Term k) (ha : Arithmetic t) {n ctx : Nat}
 (p : Program n) (old a : Program 1) (x : Program 3) (I : Installation p old a x)
 (values : List.Vector (Term ctx) k) :
 Computes p [] (LiteralTemplateQuote.templateQuote t) values (raw I.numeralTag I.consTag I.appendTag values t) := by
 let J := I.toProducers.toAdditionProducer.toEvaluation.toCurrent.toComputation.toEvaluator
 induction t with
 | var i =>
  exact unary p [] values LiteralNumeralPrefix.numeralCode (.projection i) _ _
    (projection p [] values i) (copies p [] LiteralNumeralPrefix.numeralCode I.numeralTag I.hnumeral _)
 | zero =>
  exact binary p [] values HistoryCodec.cons _ _ _ _ _
    (constantValue p [] values 1) (constantValue p [] values 0) (copies p [] HistoryCodec.cons I.consTag I.hc _)
 | succ t ih => exact RawMulNewestAdditionIteration.CombinatorProof.succ p old a x J values _ _ (ih ha)
 | add t u iht ihu => exact RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J values 3 _ _ _ _ (iht ha.1) (ihu ha.2)
 | mul t u iht ihu => exact RawMulNewestAdditionIteration.CombinatorProof.bin p old a x J values 4 _ _ _ _ (iht ha.1) (ihu ha.2)
 | universalFunction t ih => exact False.elim ha

theorem certificateComputes {k : Nat} (t : Term k) (ha : Arithmetic t) {n ctx : Nat}
 (p : Program n) (old a : Program 1) (x : Program 3) (I : Installation p old a x)
 (values : List.Vector (Term ctx) k) :
 Computes p [] (certificateProgram t) values (certificate I values t) := by
 let J := I.toProducers.toAdditionProducer.toEvaluation.toCurrent.toComputation.toEvaluator
 induction t with
 | var i =>
  exact RawMulNewestAdditionIteration.CombinatorProof.single p old a x J values _ _
   (RawMulNewestAdditionIteration.CombinatorProof.reflexive p old a x J values _ _
    (quoteComputes (.var i) ha p old a x I values))
 | zero =>
  exact RawMulNewestAdditionIteration.CombinatorProof.single p old a x J values _ _
   (RawMulNewestAdditionIteration.CombinatorProof.reflexive p old a x J values _ _
    (quoteComputes (.zero : Term k) ha p old a x I values))
 | succ t ih =>
  apply compose p [] RawSuccessorProducer.producer _ values
   (raw I.numeralTag I.consTag I.appendTag values t ::ᵥ instantiatedValue t values ::ᵥ certificate I values t ::ᵥ nil) _
  · intro i
    cases i using Fin.cases with
    | zero => exact quoteComputes t ha p old a x I values
    | succ i => cases i using Fin.cases with
      | zero => exact ValueProof.computes t ha p values
      | succ i => cases i using Fin.cases with
        | zero => exact ih ha
        | succ i => exact Fin.elim0 i
  · exact copies p [] RawSuccessorProducer.producer I.successorProducerTag I.hsuccessorProducer _
 | add t u iht ihu =>
  apply compose p [] RawAdditionProducer.producer _ values
   (raw I.numeralTag I.consTag I.appendTag values t ::ᵥ raw I.numeralTag I.consTag I.appendTag values u ::ᵥ
    instantiatedValue t values ::ᵥ instantiatedValue u values ::ᵥ certificate I values t ::ᵥ certificate I values u ::ᵥ nil) _
  · intro i
    cases i using Fin.cases with
    | zero => exact quoteComputes t ha.1 p old a x I values
    | succ i => cases i using Fin.cases with
      | zero => exact quoteComputes u ha.2 p old a x I values
      | succ i => cases i using Fin.cases with
        | zero => exact ValueProof.computes t ha.1 p values
        | succ i => cases i using Fin.cases with
          | zero => exact ValueProof.computes u ha.2 p values
          | succ i => cases i using Fin.cases with
            | zero => exact iht ha.1
            | succ i => cases i using Fin.cases with
              | zero => exact ihu ha.2
              | succ i => exact Fin.elim0 i
  · exact copies p [] RawAdditionProducer.producer I.producerTag I.hproducer _
 | mul t u iht ihu =>
  apply compose p [] RawMultiplicationProducer.producer _ values
   (raw I.numeralTag I.consTag I.appendTag values t ::ᵥ raw I.numeralTag I.consTag I.appendTag values u ::ᵥ
    instantiatedValue t values ::ᵥ instantiatedValue u values ::ᵥ certificate I values t ::ᵥ certificate I values u ::ᵥ nil) _
  · intro i
    cases i using Fin.cases with
    | zero => exact quoteComputes t ha.1 p old a x I values
    | succ i => cases i using Fin.cases with
      | zero => exact quoteComputes u ha.2 p old a x I values
      | succ i => cases i using Fin.cases with
        | zero => exact ValueProof.computes t ha.1 p values
        | succ i => cases i using Fin.cases with
          | zero => exact ValueProof.computes u ha.2 p values
          | succ i => cases i using Fin.cases with
            | zero => exact iht ha.1
            | succ i => cases i using Fin.cases with
              | zero => exact ihu ha.2
              | succ i => exact Fin.elim0 i
  · exact copies p [] RawMultiplicationProducer.producer I.multiplicationProducerTag I.hmultiplicationProducer _
 | universalFunction t ih => exact False.elim ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof.quoteComputes
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof.certificateComputes
