module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalApplicationStepPeelSupportProof (andLeft)
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem baseValue (singleton : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton (numeral 1) z))) :
 Nonempty (Derivation body Delta (programGraph tableBase singleton Fin.elim0)) :=
 binaryValue InternalListCodec.consCode (OriginalRawSyntaxTransport.constant 0 1)
   (OriginalRawSyntaxTransport.constant 0 0) singleton (numeral 1) z Fin.elim0 hc
   (constantValue 1 Fin.elim0) (constantValue 0 Fin.elim0)

theorem tableZero (singleton : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton (numeral 1) z))) :
 Nonempty (Derivation body Delta (graph1 table singleton z)) :=
 recursionZeroValue tableBase tableStep singleton Fin.elim0 (baseValue singleton hc)

theorem decoderZero (singleton : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton (numeral 1) z))) :
 Nonempty (Derivation body Delta (graph1 decoder (numeral 1) z)) :=
 unaryValue InternalListCodec.headCode table (numeral 1) singleton (Fin.cons z Fin.elim0)
   (andLeft (InternalListCodecSupportProof.consDestruction singleton (numeral 1) z hc))
   (tableZero singleton hc)

theorem actualZero : RankMemoTargets.ActualZero := by
 intro body alpha Delta
 apply programCases InternalListCodec.consCode (Fin.cons (numeral 1) (Fin.cons z Fin.elim0)) _
 intro beta j Theta singleton hj hc
 simp only [graph1,programRename,consTermRename,emptyRename,numeral,InternalTagArithmeticSyntaxProof.zRelabel,InternalTagArithmeticSyntaxProof.sucRelabel]
 simp only [consTermRename,emptyRename,numeral,InternalTagArithmeticSyntaxProof.zRelabel,InternalTagArithmeticSyntaxProof.sucRelabel] at hc
 exact decoderZero singleton hc

theorem actualNext : RankMemoTargets.ActualNext := by
 intro body alpha Delta stage old value next ho hv hc
 apply recursionNext tableBase tableStep next old stage Fin.elim0 ho
 exact binaryValue InternalListCodec.consCode nextValue (.projection 1) next value old
   (Fin.cons stage (Fin.cons old Fin.elim0)) hc hv
   (projectionValue 1 (Fin.cons stage (Fin.cons old Fin.elim0)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRecurrenceProof
