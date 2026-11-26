module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationObservationQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual internal queries discharge both child E/raw-rank computations,
all recursive-root observation nodes, the table and the numeric envelope. -/
theorem actualCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage input parameter typ raw domain children payload fnRaw argRaw fnType fnPacked argPacked rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank input)))
 (hfs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fnPacked parameter)))
 (has : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) argPacked parameter)))
 (h0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (h1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
 (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)))
 (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children fnRaw argRaw)))
 (h4 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)))
 (h5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing fnPacked fnType fnRaw)))
 (h6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing argPacked domain argRaw)))
 : Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 apply RankCalibrationApplicationObservationQueries.actualCases R domain typ fnType fnPacked argPacked parameter fnRaw argRaw _
 intro beta j Theta fnValue argValue fnRank argRank fnObserved argObserved observations typedData data candidate hj h7 h8 hfr har h9 h10 h11 h12 h13 h14
 simp only [graph1Rename,sucRelabel]
 have ih' := renameInto ih j Theta hj
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have hfs' := renameInto hfs j Theta hj
 have has' := renameInto has j Theta hj
 have h0' := renameInto h0 j Theta hj
 have h1' := renameInto h1 j Theta hj
 have h2' := renameInto h2 j Theta hj
 have h3' := renameInto h3 j Theta hj
 have h4' := renameInto h4 j Theta hj
 have h5' := renameInto h5 j Theta hj
 have h6' := renameInto h6 j Theta hj
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih' hs' hv' hr' hfs' has' h0' h1' h2' h3' h4' h5' h6'
 apply RankCalibrationEnvelopeQueries.actualCases (stage.relabel j) _
 intro delta k Xi tab base inner root rows hk ht ho hi
 simp only [graph1Rename,sucRelabel]
 have ih'' := renameInto ih' k Xi hk
 have hs'' := renameInto hs' k Xi hk
 have hv'' := renameInto hv' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have hfs'' := renameInto hfs' k Xi hk
 have has'' := renameInto has' k Xi hk
 have h0'' := renameInto h0' k Xi hk
 have h1'' := renameInto h1' k Xi hk
 have h2'' := renameInto h2' k Xi hk
 have h3'' := renameInto h3' k Xi hk
 have h4'' := renameInto h4' k Xi hk
 have h5'' := renameInto h5' k Xi hk
 have h6'' := renameInto h6' k Xi hk
 have h7'' := renameInto h7 k Xi hk
 have h8'' := renameInto h8 k Xi hk
 have h9'' := renameInto h9 k Xi hk
 have h10'' := renameInto h10 k Xi hk
 have h11'' := renameInto h11 k Xi hk
 have h12'' := renameInto h12 k Xi hk
 have h13'' := renameInto h13 k Xi hk
 have h14'' := renameInto h14 k Xi hk
 have hfr'' := renameInto hfr k Xi hk
 have har'' := renameInto har k Xi hk
 simp only [graph1Rename,graph2Rename,belowRawRename,sucRelabel,SourceComputabilityFormulaSupportProof.numeral,zRelabel] at ih'' hs'' hv'' hr'' hfs'' has'' h0'' h1'' h2'' h3'' h4'' h5'' h6'' h7'' h8'' h9'' h10'' h11'' h12'' h13'' h14'' hfr'' har''
 exact RankCalibrationApplicationCoordinatesProof.actualCoordinates R H G M W
   ((stage.relabel j).relabel k) tab ((input.relabel j).relabel k) ((parameter.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) ((domain.relabel j).relabel k) ((children.relabel j).relabel k) ((payload.relabel j).relabel k) ((fnRaw.relabel j).relabel k) ((argRaw.relabel j).relabel k) ((fnType.relabel j).relabel k) ((fnPacked.relabel j).relabel k) ((argPacked.relabel j).relabel k) (fnValue.relabel k) (argValue.relabel k) (fnObserved.relabel k) (argObserved.relabel k) (observations.relabel k) (typedData.relabel k) (data.relabel k) (candidate.relabel k) base inner root rows ((rank.relabel j).relabel k) (fnRank.relabel k) (argRank.relabel k)
   ih'' hs'' hv'' hr'' ht ho hi hfs'' has'' hfr'' har'' h0'' h1'' h2'' h3'' h4'' h5'' h6'' h7'' h8'' h9'' h10'' h11'' h12'' h13'' h14''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationQueriesProof
