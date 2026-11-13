module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Whole actual completed states agree at different arbitrary symbolic
counts, without a comparison/bound between those counts. -/
def ActualCompletedAgreement : Prop :=
 ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (first second input left right : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) left first input)) →
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty left)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) right second input)) →
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty right)) →
 Nonempty (Derivation body Delta (eqn left right))
/-- Genuine job admission is the existing literal source/weight/branching
formula. No framed-run, result-content, local-return or fixedpoint supplier
is a premise. All original runtime Programs and symbolic domains are retained. -/
def ActualFramedCompletion : Prop :=
 ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B job : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)) →
 Nonempty (Derivation body Delta (FramedCompletionDefinitions.Completion R job))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionTargets
