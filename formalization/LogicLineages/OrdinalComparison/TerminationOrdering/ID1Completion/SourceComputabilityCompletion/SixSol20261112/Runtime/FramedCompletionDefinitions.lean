module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimePaddingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalFiniteBlocks (block)
open InternalClosedPrograms (allBlock)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual codec geometry of one original visit over arbitrary work/result
backgrounds. Every displayed state is literal original runtime data. -/
def geometry {alpha : Type}
 (job value suffix old frame work input pushed output : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing frame (numeral 0) job ⊓
 (graph2 InternalListCodec.consCode work frame suffix ⊓
 (graph2 InternalPairing.pairing input work old ⊓
 (graph2 InternalListCodec.consCode pushed value old ⊓
  graph2 InternalPairing.pairing output suffix pushed)))
def framedBody {alpha : Type} (R : Program 2) (job count value : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
 (geometry (job.relabel Sum.inl) (value.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
   (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
 (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) (.var (.inr 6))
   (count.relabel Sum.inl) (.var (.inr 4)))
/-- One SAME count and value work for EVERY agenda and result background.
The original count is exact for this subtree, rather than padded while its
arbitrary agenda suffix is still present. -/
def Framed {alpha : Type} (R : Program 2) (job count value : OTerm alpha) : Formula alpha :=
 allBlock (framedBody R job count value)
def completionMatrix {alpha : Type} (R : Program 2) (job : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 Framed R (job.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
/-- Existential count/value precede all seven arbitrary background/state
coordinates; no run or result invariant is assumed in this formula. -/
def Completion {alpha : Type} (R : Program 2) (job : OTerm alpha) : Formula alpha :=
 block (completionMatrix R job)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionDefinitions
