module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The unchanged evaluator observes term jobs; the unchanged original argument
observation observes argument jobs. This is proof-side content, not a replacement
runtime or a new evaluator. -/
def contentProgram (R : Program 2) : Program 1 :=
  SixSol20261113.Context.ChildContentDefinitions.observationFromJob
    (OriginalHereditaryEvaluatorDefinitions.evaluator R)
/-- Exact content for one actual completed subtree value. -/
def Content {alpha : Type} (R : Program 2) (job value : OTerm alpha) : Formula alpha :=
  graph1 (contentProgram R) value job
/-- Internally quantified form for later arithmetic induction. The count/value
are arbitrary actual framed-run witnesses, not chosen semantic outputs. -/
def contentMatrix {alpha : Type} (R : Program 2) (job : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R
    (job.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
  (Content R (job.relabel Sum.inl) (.var (.inr 1)))
def AllFramedContent {alpha : Type} (R : Program 2) (job : OTerm alpha) : Formula alpha :=
  allBlock (contentMatrix R job)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDefinitions
