module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.SymbolicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CoreProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open SymbolicProof

def successorInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) : RawSuccessorProducer.Installation p old a x := {
 toEvaluation := I.toProducers.toAdditionProducer.toEvaluation
 producerTag := I.successorProducerTag
 hproducer := I.hsuccessorProducer }

theorem symbolicEvaluation {k : Nat} (t : Term k) (ha : Arithmetic t) {n ctx : Nat}
 (p : Program n) (old a : Program 1) (x : Program 3) (I : Installation p old a x)
 (values : List.Vector (Term ctx) k) (index fuel : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.conj (RawReflexivityDispatcher.valid I.validatorTag (raw I.numeralTag I.consTag I.appendTag values t))
   (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
    (raw I.numeralTag I.consTag I.appendTag values t)
    (LiteralNumeralPrefix.numeralCall I.numeralTag (instantiatedValue t values))
    (certificate I values t)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let J := I.toProducers.toAdditionProducer.toEvaluation.toCurrent.toComputation.toEvaluator
 induction t with
 | var i =>
  obtain ⟨hv⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x J (values.get i)
  obtain ⟨hr⟩ := RawMulLeftCongruence.ReflexivityProof.internalReflexivity n p old (RawMulNewestAddition.arithmetic a) x
   J.toAddition.toCongruence.toNewestEquality.toCongruences.toNewest ctx
   (LiteralNumeralPrefix.numeralCall I.numeralTag (values.get i)) index fuel
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) (.mp hr hv)⟩
 | zero =>
  obtain ⟨hz⟩ := LiteralNumeralPrefix.EquationsProof.zero (ctx := ctx) p I.numeralTag I.consTag I.hnumeral I.hc
  obtain ⟨hnv⟩ := RawMulNewestAdditionIteration.InvariantSupport.numeralValid p old a x J (.zero : Term ctx)
  have he := HistoryLookup.DestructorProof.unaryCallCongruence (T := T) I.validatorTag _ _ hz
  have hv := Logic.trans _ _ _ (Support.equalitySymmetry _ _ he) hnv
  obtain ⟨hc⟩ := RawUnaryEvaluation.StatementChecks.exactZero n p old a x I.toProducers.toAdditionProducer.toEvaluation ctx index fuel
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hv) hc⟩
 | succ t ih =>
  obtain ⟨hh⟩ := ih ha
  have hv := GorbowTheoryProof.Derivation.mp (.logical (.andLeft _ _)) hh
  have hc := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) hh
  obtain ⟨hvalid⟩ := RawSuccCongruence.StatementChecks.exactSuccessorValidity n p I.validatorTag I.pairTag I.consTag I.hv I.hp I.hc ctx (raw I.numeralTag I.consTag I.appendTag values t)
  obtain ⟨hprod⟩ := RawSuccessorProducer.StatementChecks.exactEvaluation n p old a x (successorInstallation p old a x I) ctx
   (raw I.numeralTag I.consTag I.appendTag values t) (instantiatedValue t values) (certificate I values t) index fuel
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) (.mp hvalid hv)) (.mp (.mp hprod hv) hc)⟩
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht ha.1
  obtain ⟨hu⟩ := ihu ha.2
  have htv := GorbowTheoryProof.Derivation.mp (.logical (.andLeft _ _)) ht
  have htc := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) ht
  have huv := GorbowTheoryProof.Derivation.mp (.logical (.andLeft _ _)) hu
  have huc := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) hu
  obtain ⟨hvalid⟩ := RawAdditionComputation.ValidityProof.internalAdditionValidity n p I.validatorTag I.pairTag I.consTag I.appendTag I.hv I.hp I.hc I.ha ctx
   (raw I.numeralTag I.consTag I.appendTag values t) (raw I.numeralTag I.consTag I.appendTag values u)
  obtain ⟨hprod⟩ := RawAdditionProducer.StatementChecks.exactEvaluation n p old a x I.toProducers.toAdditionProducer ctx
   (raw I.numeralTag I.consTag I.appendTag values t) (raw I.numeralTag I.consTag I.appendTag values u)
   (instantiatedValue t values) (instantiatedValue u values) (certificate I values t) (certificate I values u) index fuel
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) (.mp (.mp hvalid htv) huv)) (.mp (.mp (.mp (.mp hprod htv) huv) htc) huc)⟩
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht ha.1
  obtain ⟨hu⟩ := ihu ha.2
  have htv := GorbowTheoryProof.Derivation.mp (.logical (.andLeft _ _)) ht
  have htc := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) ht
  have huv := GorbowTheoryProof.Derivation.mp (.logical (.andLeft _ _)) hu
  have huc := GorbowTheoryProof.Derivation.mp (.logical (.andRight _ _)) hu
  obtain ⟨hvalid⟩ := RawMultiplicationComputation.ValidityProof.internalMultiplicationValidity n p I.validatorTag I.pairTag I.consTag I.appendTag I.hv I.hp I.hc I.ha ctx
   (raw I.numeralTag I.consTag I.appendTag values t) (raw I.numeralTag I.consTag I.appendTag values u)
  obtain ⟨hprod⟩ := RawMultiplicationProducer.StatementChecks.exactEvaluation n p old a x I.toProducers ctx
   (raw I.numeralTag I.consTag I.appendTag values t) (raw I.numeralTag I.consTag I.appendTag values u)
   (instantiatedValue t values) (instantiatedValue u values) (certificate I values t) (certificate I values u) index fuel
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) (.mp (.mp hvalid htv) huv)) (.mp (.mp (.mp (.mp hprod htv) huv) htc) huc)⟩
 | universalFunction t ih => exact False.elim ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CoreProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CoreProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.CoreProof.symbolicEvaluation
