module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleRelationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorErasureSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem symmetric (R : Program 2) (left right parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (SameEvaluator R left right parameter))) :
 Nonempty (Derivation body Delta (SameEvaluator R right left parameter)) := by
 apply sameCases R left right parameter _ h
 intro beta j Theta value hj hv
 rw [sameRename]
 exact sameIntro R (right.relabel j) (left.relabel j) (parameter.relabel j) value
   (andIntro (andRight hv) (andLeft hv))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleRelationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleRelationProof
