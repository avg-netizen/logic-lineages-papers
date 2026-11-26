module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every actual bounded lookup has one count/value uniformly valid over
all backgrounds. This is the explicit recursive job-completion supplier. -/
def allBody {alpha : Type} (R : Program 2) (size jobs : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (OriginalContextInsertion.Below (.var (.inr 0)) (size.relabel Sum.inl) ⊓
  graph2 InternalRawListRecursion.lookup (.var (.inr 1)) (.var (.inr 0)) (jobs.relabel Sum.inl)).imp
 (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R (.var (.inr 1)))
def AllComplete {alpha : Type} (R : Program 2) (size jobs : OTerm alpha) : Formula alpha :=
 allBlock (allBody R size jobs)
def completionMatrix {alpha : Type} (R : Program 2) (size tagged : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 OriginalContextInsertion.lengthGraph (size.relabel Sum.inl) (.var (.inr 1)) ⊓
 PrefixFrameDefinitions.PrefixFrame R (tagged.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
/-- One exact run count and produced row precede all arbitrary backgrounds.
The resulting row contains exactly one result for each original visit. -/
def Completion {alpha : Type} (R : Program 2) (size tagged : OTerm alpha) : Formula alpha :=
 block (completionMatrix R size tagged)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionDefinitions
