module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentInductionBinding
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions RankArgumentInductionDefinitions RankArgumentInductionSyntax
open RankArgumentInductionBinding SortWeightedDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {k : Nat}
variable (Q : Program 2) (F : Program (k+1)) (H : Program 1) (M W : Program 2)
attribute [local irreducible] programGraph
theorem fieldsRename {beta : Type} (parameter gamma c bound raw types observations rank : OTerm alpha)
 (j : alpha → beta) :
 (fields Q H M W parameter gamma c bound raw types observations rank).relabel j =
 fields Q H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j) (bound.relabel j)
   (raw.relabel j) (types.relabel j) (observations.relabel j) (rank.relabel j) := by
 simp only [fields,conjunctionRename,argumentsAcceptedRename,graph1Rename,graph2Rename,RankArgumentSyntax.smallRename]
theorem consQuery (parameter gamma c bound raw types observations rank typ child tail tailTypes : OTerm alpha)
 (params : Fin k → OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw Q F H M W parameter gamma c bound raw params)))
 (hw : Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)))
 (hf : Nonempty (Derivation body Delta (fields Q H M W parameter gamma c bound raw types observations rank)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hh : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ child gamma c)))
 (ht : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W tailTypes tail gamma c)))
 (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess tail raw))) :
 Nonempty (Derivation body Delta (programGraph (weighted F) rank (Fin.cons observations params))) := by
 apply RankArgumentQueries.consQueries Q typ child tail parameter _
 intro beta j Theta packed observation typed mappedTail headRank tailRank hj hp ho htyped hm hhr htr
 simp only [programRename,consTermRename]
 have hi' := renameInto hi j Theta hj
 rw [belowRawRename] at hi'
 have hw' := renameInto hw j Theta hj
 rw [RankArgumentSyntax.weightsRename] at hw'
 have hf' := renameInto hf j Theta hj
 rw [fieldsRename] at hf'
 have hc' := renameInto hc j Theta hj
 rw [graph3Rename] at hc'
 have hh' := renameInto hh j Theta hj
 rw [termAcceptedRename] at hh'
 have ht' := renameInto ht j Theta hj
 rw [argumentsAcceptedRename] at ht'
 have hlt' := renameInto hlt j Theta hj
 simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 have hobs := andLeft (andRight hf')
 have hrank := andLeft (andRight (andRight hf'))
 have hsmall := andRight (andRight (andRight hf'))
 have hcons := OriginalTypedArgumentObservationsInternalConsProof.forward Q (raw.relabel j) (typ.relabel j)
   (child.relabel j) (tail.relabel j) packed observation typed mappedTail (parameter.relabel j)
   (observations.relabel j) hc' hp ho htyped hm hobs
 have htailSmall := RankArgumentSmallProof.tailSmall (observations.relabel j) typed mappedTail (bound.relabel j) hsmall hcons
 have htailAt := belowRawAt Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j)
   (bound.relabel j) (raw.relabel j) (tail.relabel j) (fun i => (params i).relabel j) hi' hlt'
 have htailFields : Nonempty (Derivation body Theta (fields Q H M W (parameter.relabel j)
   (gamma.relabel j) (c.relabel j) (bound.relabel j) (tail.relabel j) (tailTypes.relabel j) mappedTail tailRank)) :=
   andIntro ht' (andIntro hm (andIntro htr htailSmall))
 have hfold := atRawApply Q F H M W (parameter.relabel j) (gamma.relabel j) (c.relabel j)
   (bound.relabel j) (tail.relabel j) (tailTypes.relabel j) mappedTail tailRank
   (fun i => (params i).relabel j) htailAt htailFields
 exact RankArgumentConsProof.consAtValues Q F H M W (raw.relabel j) (typ.relabel j)
   (child.relabel j) (tail.relabel j) packed observation typed mappedTail (parameter.relabel j)
   (gamma.relabel j) (c.relabel j) (observations.relabel j) (rank.relabel j) headRank tailRank
   (bound.relabel j) (fun i => (params i).relabel j) hc' hp ho htyped hm hobs hh' hrank hhr htr hsmall hw' hfold
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentCoreProof
