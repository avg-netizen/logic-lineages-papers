module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Explicitly CONDITIONAL local construction: genuinely admitted parent and
completion of every actual expanded job suffice. This is NOT the final theorem;
the descendant completion premise is discharged by internal weight induction. -/
def ActualLocalCompletion : Prop :=
 ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B job jobs size : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs)) →
 Nonempty (Derivation body Delta (VisitListCompletionDefinitions.AllComplete R size jobs)) →
 Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job))
/-- Internal arithmetic strong-induction result, with no assumption that any
job or descendant already completes. -/
def ActualBelowCompletion : Prop :=
 ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B bound : OTerm alpha),
 Nonempty (Derivation body Delta (SourceFramedDefinitions.BelowCompletion R H M W c B bound))
/-- EXACT unchanged original full framed-completion target from 12 November.
No child-completion, local-frame, root-content, native-calibration or weakened
source predicate is added. Count and value still precede arbitrary backgrounds. -/
def ActualSourceFramedCompletion : Prop :=
 SixSol20261112.Runtime.FramedCompletionTargets.ActualFramedCompletion
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedTargets
