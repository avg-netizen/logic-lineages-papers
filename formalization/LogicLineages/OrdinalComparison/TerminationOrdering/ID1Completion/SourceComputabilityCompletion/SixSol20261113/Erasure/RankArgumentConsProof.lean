module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSmallProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof (symm)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions SortWeightedDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem consAtValues {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2)
 (raw typ child tail packed observation typed mappedTail parameter gamma c out rank headRank tailRank bound : OTerm alpha)
 (params : Fin k → OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 Q observation packed parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ observation)))
 (hm : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) mappedTail tail parameter)))
 (hout : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) out raw parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ child gamma c)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw)))
 (hh : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw headRank child)))
 (htail : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw tailRank tail)))
 (hs : Nonempty (Derivation body Delta (AllSmall out bound)))
 (hw : Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)))
 (hfold : Nonempty (Derivation body Delta (programGraph (weighted F) tailRank (Fin.cons mappedTail params)))) :
 Nonempty (Derivation body Delta (programGraph (weighted F) rank (Fin.cons out params))) := by
 have hcons := OriginalTypedArgumentObservationsInternalConsProof.forward Q raw typ child tail packed
   observation typed mappedTail parameter out hc hp ho ht hm hout
 have hsmall := RankArgumentSmallProof.headSmall out typed mappedTail typ observation bound hs hcons ht
 have hweight := RankArgumentLocalProof.weightApply Q F H M W parameter gamma c bound params
   typ child packed observation typed headRank hw ha hp ho ht hh hsmall
 have hsum := OriginalRawVariableRankSupportProof.rankSumForward rank child tail headRank tailRank hh htail
   (OriginalRawVariableRankConsProof.rankConsForward raw rank typ child tail hc hr)
 have he := valueUnique InternalArithmeticPrograms.addition rank (add headRank tailRank)
   (Fin.cons headRank (Fin.cons tailRank Fin.elim0)) hsum
   (InternalArithmeticProgramsSupportProof.additionValue headRank tailRank)
 obtain ⟨he⟩ := he
 exact outputTransport (weighted F) (add headRank tailRank) rank (Fin.cons out params) ⟨symm he⟩
   (SortWeightedFoldProof.consValue F out typed mappedTail headRank tailRank params hcons hweight hfold)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentConsProof
