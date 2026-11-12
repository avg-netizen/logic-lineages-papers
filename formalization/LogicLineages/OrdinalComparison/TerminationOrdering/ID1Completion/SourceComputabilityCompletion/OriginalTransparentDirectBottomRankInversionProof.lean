module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableErasureCertificateRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankInversionProof
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


open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof

theorem unaryInput (P : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 1)
 (out x y : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal x y)))
 (hp : Nonempty (Derivation body Delta (graph1 P out x))) :
 Nonempty (Derivation body Delta (graph1 P out y)) := by
 apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 1 Delta _ out
  (Fin.cons x Fin.elim0) (Fin.cons y Fin.elim0) ?_ hp
 intro i
 exact Fin.cases he (fun j => Fin.elim0 j) i

theorem tagAtBottom (erased typ rawE bottomRaw : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erased typ rawE)))
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode erased typ)))
 (hr : Nonempty (Derivation body Delta (graph1 bottomConstructor bottomRaw typ))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 3) rawE)) := by
 have hp := bottomCodePair erased bottomRaw typ hr hb
 have eq := valueUnique InternalUnpair.right bottomRaw rawE (Fin.cons erased Fin.elim0)
  (pairRight erased typ bottomRaw hp) (pairRight erased typ rawE he)
 have ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 3) bottomRaw)) :=
  bottomTag (.projection 0) bottomRaw typ ![bottomRaw] (projectionValue 0 ![bottomRaw]) hr
 exact unaryInput rawTag (numeral 3) bottomRaw rawE eq ht

theorem originalTagZero (s erased typ raw rawE bottomRaw d cutoff tag : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
 (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erased typ rawE)))
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode erased typ)))
 (hr : Nonempty (Derivation body Delta (graph1 bottomConstructor bottomRaw typ)))
 (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
 (her : Nonempty (Derivation body Delta (graph3 eraseRaw rawE d cutoff raw)))
 (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (numeral 1) s).not)) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 0) raw)) := by
 let E : Formula alpha := equal tag (numeral 0)
 apply InternalOriginalPairingOrderArithmeticProof.formulaCases E _
 · exact outputTransport rawTag tag (numeral 0) (Fin.cons raw Fin.elim0)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ht E)
 · have htag := tagAtBottom erased typ rawE bottomRaw
    (withHyp he E.not) (withHyp hb E.not) (withHyp hr E.not)
   have eq := OriginalRawErasureBottomInversionProof.bottomInversion raw rawE d cutoff tag
    (withHyp ht E.not) ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp her E.not) htag
   have b := OriginalTransparentDirectBottomRankPairProof.bottomFromSameRaw s erased typ raw rawE
    (withHyp hs E.not) (withHyp he E.not) eq (withHyp hb E.not)
   obtain ⟨nb⟩ := withHyp hn E.not
   obtain ⟨b⟩ := b
   exact ⟨Derivation.explosion (Derivation.implicationElimination nb b)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankInversionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankInversionProof
