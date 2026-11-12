module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryEvaluatorDefinitions
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof (constantEvaluation)
open OriginalHereditaryVisitSchedulerEvaluationProof (headNumeric projectionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
attribute [local irreducible] OriginalHereditaryFuelProgram.fuel OriginalHereditaryRuntimeIterationDefinitions.run

theorem jobEvaluation (packed parameter : Nat) :
 evaluate job (ofFn ![packed,parameter]) = Nat.pair 0
   (Nat.pair (Nat.unpair packed).1 (Nat.pair (Nat.unpair packed).2 parameter)) := by
 simp only [job,pairOfEvaluation,leftOfEvaluation,rightOfEvaluation,constantEvaluation,
   projectionEvaluation,get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem initialEvaluation (packed parameter : Nat) :
 evaluate initial (ofFn ![packed,parameter]) = Nat.pair
   (1 + Nat.pair (Nat.pair 0 (evaluate job (ofFn ![packed,parameter]))) 0) 0 := by
 simp only [initial,pairOfEvaluation,consOfEvaluation,constantEvaluation]

theorem evaluation (R : Program 2) (packed parameter : Nat) :
 evaluate (evaluator R) (ofFn ![packed,parameter]) =
 (Nat.unpair ((Nat.unpair (evaluate (OriginalHereditaryRuntimeIterationDefinitions.run R)
   (ofFn ![evaluate OriginalHereditaryFuelProgram.fuel
     (ofFn ![evaluate job (ofFn ![packed,parameter])]),evaluate initial (ofFn ![packed,parameter])]))).2 - 1)).1 := by
 simp only [evaluator,completed,computedFuel,evaluate,rightOfEvaluation,vectorOne,vectorTwo,
   get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,headNumeric]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorEvaluationProof
