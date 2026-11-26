module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankPairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalRawSyntaxTransport OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawVariableRankSupportProof OriginalRawVariableRankLeafProof
open OriginalVariableErasureCertificateRawProof (equalRefl bottomCodePair)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


theorem pairSecond (out typ raw other : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal raw other)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out typ raw))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out typ other)) := by
 apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
  _ out ![typ,raw] ![typ,other] ?_ hp
 intro i
 refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
 · change Nonempty (Derivation body Delta (equal typ typ))
   exact equalRefl typ
 · exact he

theorem bottomFromSameRaw (s erased typ raw rawE : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
 (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erased typ rawE)))
 (hraw : Nonempty (Derivation body Delta (equal rawE raw)))
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode erased typ))) :
 Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (numeral 1) s)) := by
 have hp := pairSecond erased typ rawE raw hraw he
 have eq := valueUnique InternalPairing.pairing erased s ![typ,raw] hp hs
 exact BottomSourceShapeProof.bottomAccept s typ
  (outputTransport BottomRepresentative.bottomCode erased s (Fin.cons typ Fin.elim0) eq hb)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankPairProof
