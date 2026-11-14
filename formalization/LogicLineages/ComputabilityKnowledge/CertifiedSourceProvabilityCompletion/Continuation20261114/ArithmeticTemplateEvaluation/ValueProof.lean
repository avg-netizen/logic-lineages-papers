module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.ValueProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem computes {k : Nat} (t : Term k) (ha : Arithmetic t) {n ctx : Nat} (p : Program n)
 (values : List.Vector (Term ctx) k) :
 Computes p [] (valueProgram t) values (instantiatedValue t values) := by
 induction t with
 | var i => exact projection p [] values i
 | zero => exact constantValue p [] values 0
 | succ t ih =>
  apply unary p [] values .succ (valueProgram t) (instantiatedValue t values) (.succ (instantiatedValue t values)) (ih ha)
  intro tag ht
  obtain ⟨h⟩ := Support.intoRegistry p .succ tag ht _
   (NamedArithmeticGraph.Equations.successor tag ctx (instantiatedValue t values ::ᵥ nil))
  exact ⟨.base h⟩
 | add t u iht ihu =>
  apply binary p [] values HistoryCodec.add (valueProgram u) (valueProgram t)
   (instantiatedValue u values) (instantiatedValue t values)
   (.add (instantiatedValue t values) (instantiatedValue u values)) (ihu ha.2) (iht ha.1)
  intro tag ht
  obtain ⟨h⟩ := HistoryCodec.StatementChecks.internalAdd n p tag ht ctx (instantiatedValue u values) (instantiatedValue t values)
  exact ⟨.base h⟩
 | mul t u iht ihu =>
  apply binary p [] values HistoryCodec.multiply (valueProgram u) (valueProgram t)
   (instantiatedValue u values) (instantiatedValue t values)
   (.mul (instantiatedValue t values) (instantiatedValue u values)) (ihu ha.2) (iht ha.1)
  intro tag ht
  obtain ⟨h⟩ := HistoryCodec.StatementChecks.internalMultiply n p tag ht ctx (instantiatedValue u values) (instantiatedValue t values)
  exact ⟨.base h⟩
 | universalFunction t ih => exact False.elim ha

theorem internalValue : Targets.InternalValue := by
 intro k t ha n p old a x I J ctx values
 obtain ⟨h⟩ := computes t ha p values J.valueTag J.hvalue
 exact ⟨Hilbert.Local.finish h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.ValueProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.ValueProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.ValueProof.computes
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.ValueProof.internalValue
