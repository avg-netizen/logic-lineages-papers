module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Distinct symbolic completion counts for the same actual job cannot change
its returned value. No admission or ordering relation between counts is needed. -/
def ActualFramedValueAgreement : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (job first second left right : OTerm alpha),
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job first left)) →
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job second right)) →
 Nonempty (Derivation body Delta (eqn left right))
/-- Exact role-zero half of the original framed-content target, at the supplied
actual returned value. No source-G test, native calibration, or result-content
premise is added. The original Job supplies all source admission. -/
def ActualTermFramedContent : Prop := ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B job count value : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 0) job)) →
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)) →
 Nonempty (Derivation body Delta (graph1
   (SixSol20261113.Context.ChildContentDefinitions.observationFromJob (OriginalHereditaryEvaluatorDefinitions.evaluator R)) value job))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.FramedValueTargets
