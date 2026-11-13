module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationRootEncodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual source lambda coordinates discharge child admission, child rank,
recursive-root identification, numeric descent and memo dispatch. Remaining
query wrappers only supply these actual constructor/evaluator graph values. -/
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab input parameter arrow raw domain codomain payload childRaw childPacked context gamma extended childParam
 childValue observed typedData data candidate base inner root rows rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank input)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input arrow raw)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 1) payload)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain childRaw)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow domain codomain)))
 (h4 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childPacked codomain childRaw)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (h7 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam context extended)))
 (h8 : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) childValue childPacked childParam)))
 (h9 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing observed codomain childValue)))
 (h10 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedData codomain observed)))
 (h11 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing data domain typedData)))
 (h12 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate (numeral 1) data)))
 : Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 have hchildSource := andRight (OriginalTypedDecoderTransportLogicalProof.iffForward
   (OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof.sourceLambdaCoordinatesIff H G M W
     input parameter arrow raw payload domain childRaw domain codomain childPacked context gamma extended childParam
     h0 h1 h2 (OriginalTypedDecoderInternalListProof.consArrowFields arrow domain codomain h3) h4 h5 h6 h7) hs)
 let xs : Fin 2 → OTerm alpha := ![domain,childRaw]
 have hpair := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
   payload domain childRaw xs h2 (projectionValue 0 xs) (projectionValue 1 xs)
 have hlambda := binaryValue InternalPairing.pairing (constant 2 1)
   (pairOf (.projection 0) (.projection 1)) raw (numeral 1) payload xs
   h1 (constantValue 1 xs) hpair
 have hchildRank := rankPackedBackward childPacked rank codomain childRaw h4
   (OriginalRawVariableRankUnaryProof.rankLambdaForward raw rank domain childRaw hlambda
     (rankPackedForward input rank arrow raw h0 hr))
 have hc := OriginalRootObservationInternalProof.lambdaLaw
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) body alpha Delta
   input parameter arrow raw domain codomain payload childRaw childPacked context gamma extended childParam
   childValue observed typedData data candidate h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
 have hroot := RankCalibrationRootEncodingProof.actualEncoding R H G M W
   input parameter (suc stage) inner base root rows candidate (numeral 1) data hs hv ho hi hc h12
 exact RankCalibrationLambdaStepProof.actualStep R H G M W
   stage tab base inner root rows data observed codomain childPacked childParam childValue rank
   ih ho hi hroot (RankCalibrationSelectorProof.lambdaValue data domain typedData codomain observed h11 h10)
   h9 hchildSource h8 hchildRank ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaCoordinatesProof
