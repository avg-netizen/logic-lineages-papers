module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseEnvelopeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (suc sucRelabel)

theorem variable (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter typ raw field rank : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw field)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 0) input))) :
 Nonempty (Derivation body Delta (graph1 RankMemoDefinitions.decoder rank (suc stage))) := by
 apply RankCalibrationEnvelopeQueries.actualCases stage _
 intro beta j Theta tab base inner root rows hj htab ho hi
 simp only [graph1Rename,sucRelabel]
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have hp' := renameInto hp j Theta hj
 have hc' := renameInto hc j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs' hv' hr' hp' hc' ht'
 have htag := RankCalibrationBaseEnvelopeProof.memoTag R H G M W 0
   (stage.relabel j) tab (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) base inner root rows
   hs' hv' hp' ht' ho hi
 exact RankCalibrationLeafProof.variableSuccessor (stage.relabel j) tab (input.relabel j) (typ.relabel j)
   (raw.relabel j) (field.relabel j) (rank.relabel j) hp' hc' hr' htab htag

theorem bottom (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter typ raw field rank : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor raw field)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 3) input))) :
 Nonempty (Derivation body Delta (graph1 RankMemoDefinitions.decoder rank (suc stage))) := by
 apply RankCalibrationEnvelopeQueries.actualCases stage _
 intro beta j Theta tab base inner root rows hj htab ho hi
 simp only [graph1Rename,sucRelabel]
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have hp' := renameInto hp j Theta hj
 have hc' := renameInto hc j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hs' hv' hr' hp' hc' ht'
 have htag := RankCalibrationBaseEnvelopeProof.memoTag R H G M W 3
   (stage.relabel j) tab (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) base inner root rows
   hs' hv' hp' ht' ho hi
 exact RankCalibrationLeafProof.bottomSuccessor (stage.relabel j) tab (input.relabel j) (typ.relabel j)
   (raw.relabel j) (field.relabel j) (rank.relabel j) hp' hc' hr' htab htag
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseSuccessorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseSuccessorProof
