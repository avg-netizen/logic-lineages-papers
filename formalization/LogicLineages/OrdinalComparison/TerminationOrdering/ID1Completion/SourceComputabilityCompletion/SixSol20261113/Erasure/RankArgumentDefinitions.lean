module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every genuinely in-range typed observation has a smaller child code.
All lookup/type/pair witnesses live inside the arithmetic universal block. -/
def smallMatrix {alpha : Type} (observations bound : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 (OriginalContextInsertion.lengthGraph (.var (.inr 0)) (observations.relabel Sum.inl) ⊓
  (OriginalContextInsertion.Below (.var (.inr 1)) (.var (.inr 0)) ⊓
  (graph2 InternalRawListRecursion.lookup (.var (.inr 2)) (.var (.inr 1)) (observations.relabel Sum.inl) ⊓
   graph2 InternalPairing.pairing (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))))).imp
 (InternalLessThan.strictLess (.var (.inr 4)) (bound.relabel Sum.inl))
def AllSmall {alpha : Type} (observations bound : OTerm alpha) : Formula alpha :=
 allBlock (smallMatrix observations bound)
/-- A local bounded weighting hypothesis for genuine original admitted term
children. It is not the final whole-spine calibration conclusion. All six
coordinates (type,raw,packed,childE,typedObservation,rank) are internal. -/
def weightMatrix {alpha : Type} {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (parameter gamma c bound : OTerm alpha)
 (params : Fin k → OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W
    (.var (.inr 0)) (.var (.inr 1)) (gamma.relabel Sum.inl) (c.relabel Sum.inl) ⊓
  (graph2 InternalPairing.pairing (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1)) ⊓
  (graph2 Q (.var (.inr 3)) (.var (.inr 2)) (parameter.relabel Sum.inl) ⊓
  (graph2 InternalPairing.pairing (.var (.inr 4)) (.var (.inr 0)) (.var (.inr 3)) ⊓
  (graph1 OriginalRawSyntaxTransport.variableRankRaw (.var (.inr 5)) (.var (.inr 1)) ⊓
   InternalLessThan.strictLess (.var (.inr 3)) (bound.relabel Sum.inl)))))).imp
 (programGraph F (.var (.inr 5)) (Fin.cons (.var (.inr 4)) (fun i => (params i).relabel Sum.inl)))
def LocalWeights {alpha : Type} {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (parameter gamma c bound : OTerm alpha)
 (params : Fin k → OTerm alpha) : Formula alpha :=
 allBlock (weightMatrix Q F H M W parameter gamma c bound params)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentDefinitions
