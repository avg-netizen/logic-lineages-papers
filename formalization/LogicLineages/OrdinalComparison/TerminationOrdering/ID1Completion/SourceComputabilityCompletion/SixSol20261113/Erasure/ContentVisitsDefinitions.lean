module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every actual bounded job carries framed-run content at the unchanged evaluator.
Completion is separate: this universal alone does not assert a run exists. -/
def allBody {alpha : Type} (R : Program 2) (size jobs : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (OriginalContextInsertion.Below (.var (.inr 0)) (size.relabel Sum.inl) ⊓
  graph2 InternalRawListRecursion.lookup (.var (.inr 1)) (.var (.inr 0)) (jobs.relabel Sum.inl)).imp
 (FramedContentDefinitions.AllFramedContent R (.var (.inr 1)))
def AllContent {alpha : Type} (R : Program 2) (size jobs : OTerm alpha) : Formula alpha :=
 allBlock (allBody R size jobs)
def countMatrix {alpha : Type} (R : Program 2) (tagged produced : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 Runtime.PrefixFrameDefinitions.PrefixFrame R (tagged.relabel Sum.inl)
   (.var (.inr 0)) (produced.relabel Sum.inl)
/-- The produced row is fixed BEFORE the existential count; no length-only
replacement or existential choice of different result content is allowed. -/
def Counted {alpha : Type} (R : Program 2) (tagged produced : OTerm alpha) : Formula alpha :=
 block (countMatrix R tagged produced)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsDefinitions
