module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.CallEncoding
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphOperands
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem input {arity m ctx : Nat} (p : Program arity) (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin m) :
 Computes p ((inputPrograms m).get i) (target ::ᵥ inputs) (inputs.get i) := by
 simpa only [inputPrograms,List.Vector.get_ofFn,List.Vector.get_cons_succ] using projection p (target ::ᵥ inputs) i.succ

theorem raw {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : Tags n) (I : Installation p f g F G J)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin m) :
 Computes p ((rawPrograms m).get i) (target ::ᵥ inputs) (LiteralNumeralPrefix.numeralCall J.C.numeralTag (inputs.get i)) := by
 have h := unary p (target ::ᵥ inputs) LiteralNumeralPrefix.numeralCode J.C.numeralTag I.primitives.hn
   ((inputPrograms m).get i) (inputs.get i) (input p target inputs i)
 simp only [rawPrograms,List.Vector.get_map,LiteralNumeralPrefix.numeralCall]
 exact h

theorem actualArgument {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : Tags n) (I : Installation p f g F G J)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin n) :
 Computes p ((argumentValues g).get i) (target ::ᵥ inputs) (call (J.argumentTags i) inputs) := by
 simp only [argumentValues,List.Vector.get_ofFn]
 exact CurrentRecursionAccumulator.GraphSupport.composition p _ (g i) (J.argumentTags i) (I.hg i) _ inputs (input p target inputs)

theorem actualChild {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : Tags n) (I : Installation p f g F G J)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin n) :
 Computes p ((argumentCodes f g G).get i) (target ::ᵥ inputs)
  (call (J.argumentProducerTags i) (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target ::ᵥ inputs)) := by
 simp only [argumentCodes,List.Vector.get_ofFn]
 apply CurrentRecursionAccumulator.GraphSupport.composition p _ (G i) (J.argumentProducerTags i) (I.hG i) _
  (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target ::ᵥ inputs)
 intro j
 cases j using Fin.cases with
 | zero => exact CurrentRecursionStepProgram.EvaluatorGraph.shiftGraph p _ (argumentTag f g i) (.projection 0) target (projection p _ 0)
 | succ j => exact input p target inputs j

theorem quotedArgument {arity m n ctx : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : Tags n) (I : Installation p f g F G J)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) (i : Fin n) :
 Computes p ((argumentCalls f g).get i) (target ::ᵥ inputs)
  (callValue J.C (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target)
   (inputs.map (LiteralNumeralPrefix.numeralCall J.C.numeralTag))) := by
 simp only [argumentCalls,List.Vector.get_ofFn]
 apply CallEncoding.graph p _ J.C I.primitives _ _ _ _
  (CurrentRecursionStepProgram.EvaluatorGraph.shiftGraph p _ (argumentTag f g i) (.projection 0) target (projection p _ 0))
 intro j
 simpa only [List.Vector.get_map] using raw p f g F G J I target inputs j

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphOperands
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphOperands
