module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankValuesProof
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

theorem variableRank (raw : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 0) raw))) :
 Nonempty (Derivation body Delta (graph1 variableRankRaw (numeral 1) raw)) := by
 apply OriginalRawSyntaxTransportInternalCancellationLeafProof.variableCases raw _ ht
 intro beta rho Theta index hrho hc
 rw [graph1Rename,numeralRename]
 exact rankVariableBackward (raw.relabel rho) (numeral 1) index hc (equalRefl (numeral 1))

theorem packedRanks (s t typ raw bottomRaw : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
 (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 0) raw)))
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
 (hr : Nonempty (Derivation body Delta (graph1 bottomConstructor bottomRaw typ))) :
 Nonempty (Derivation body Delta (OriginalLambdaOriginalRankDefinitions.PackedRankDrop s t (numeral 1) (numeral 0))) := by
 have sr := rankPackedBackward s (numeral 1) typ raw hs (variableRank raw ht)
 have tr := rankPackedBackward t (numeral 0) typ bottomRaw (bottomCodePair t bottomRaw typ hr hb)
  (rankBottomBackward bottomRaw (numeral 0) typ hr (equalRefl (numeral 0)))
 exact andIntro sr (andIntro tr ⟨InternalQuotientComparisonProof.zeroLessSuccessor InternalTagArithmeticSyntaxProof.z⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankValuesProof
