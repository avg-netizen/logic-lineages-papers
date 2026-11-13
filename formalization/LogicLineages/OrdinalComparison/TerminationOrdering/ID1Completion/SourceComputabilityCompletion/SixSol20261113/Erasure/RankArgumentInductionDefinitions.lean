module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions
variable {alpha : Type} {k : Nat}
def fields (Q : Program 2) (H : Program 1) (M W : Program 2)
 (parameter gamma c bound raw types observations rank : OTerm alpha) : Formula alpha :=
 OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma c ⊓
 (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) observations raw parameter ⊓
 (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw ⊓ AllSmall observations bound))
def matrix (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
 (parameter gamma c bound raw : OTerm alpha) (params : Fin k → OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (fields Q H M W (parameter.relabel Sum.inl) (gamma.relabel Sum.inl)
   (c.relabel Sum.inl) (bound.relabel Sum.inl) (raw.relabel Sum.inl)
   (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (programGraph (SortWeightedDefinitions.weighted F) (.var (.inr 2))
   (Fin.cons (.var (.inr 1)) (fun i => (params i).relabel Sum.inl)))
def AtRaw (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
 (parameter gamma c bound raw : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix Q F H M W parameter gamma c bound raw params)
def rawPredicate (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
 (parameter gamma c bound : OTerm alpha) (params : Fin k → OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 AtRaw Q F H M W (parameter.relabel Sum.inl) (gamma.relabel Sum.inl)
   (c.relabel Sum.inl) (bound.relabel Sum.inl) (.var (.inr 0)) (fun i => (params i).relabel Sum.inl)
def BelowRaw (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
 (parameter gamma c bound raw : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
 InternalStrongInduction.below (rawPredicate Q F H M W parameter gamma c bound params) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionDefinitions
