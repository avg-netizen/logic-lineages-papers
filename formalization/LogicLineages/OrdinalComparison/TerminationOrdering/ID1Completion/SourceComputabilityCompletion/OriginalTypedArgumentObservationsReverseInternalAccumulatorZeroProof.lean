module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorZeroProof
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof (unaryVectorRename binaryVectorRename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransport (succOf constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedArgumentObservations (reverseRun reverse)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev originalRun : Program 1 := .composition reverseRun
 ![succOf (.projection 0),pairOf (.projection 0) (constant 1 0)]

theorem originalRunValue (raw state terminal : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state))) :
 Nonempty (Derivation body Delta (graph1 originalRun terminal raw)) := by
 have hi := binaryValue InternalPairing.pairing (.projection 0) (constant 1 0)
   state raw z ![raw] hp (projectionValue 0 ![raw]) (constantValue 0 ![raw])
 have hf := unaryValue (body := body) (Gamma := Delta) .succ (.projection (0 : Fin 1))
   (suc raw) raw ![raw] (successorValue ![raw]) (projectionValue 0 ![raw])
 exact binaryValue reverseRun (succOf (.projection 0)) (pairOf (.projection 0) (constant 1 0))
   terminal (suc raw) state ![raw] hr hf hi

theorem originalValue (raw state terminal result : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state)))
 (hv : Nonempty (Derivation body Delta (graph1 InternalUnpair.right result terminal))) :
 Nonempty (Derivation body Delta (graph1 reverse result raw)) :=
 unaryValue InternalUnpair.right originalRun result terminal ![raw] hv (originalRunValue raw state terminal hp hr)

theorem originalRecover (raw state terminal result : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state)))
 (hv : Nonempty (Derivation body Delta (graph1 reverse result raw))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right result terminal)) :=
 unaryRecover InternalUnpair.right originalRun result terminal ![raw] hv (originalRunValue raw state terminal hp hr)

theorem zeroAt (raw out state terminal : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state))) :
 Nonempty (Derivation body Delta ((graph2 accumulated out raw z).iff (graph1 reverse out raw))) := by
 let P := graph2 accumulated out raw z
 let Q := graph1 reverse out raw
 have hf : Nonempty (Derivation body (P :: Delta) Q) :=
   originalValue raw state terminal out (withHyp hp P) (withHyp hr P)
     (recoverRight raw z state terminal out (withHyp hp P) (withHyp hr P)
       ⟨Derivation.hypothesis List.mem_cons_self⟩)
 have hb : Nonempty (Derivation body (Q :: Delta) P) :=
   value raw z state terminal out (withHyp hp Q) (withHyp hr Q)
     (originalRecover raw state terminal out (withHyp hp Q) (withHyp hr Q)
       ⟨Derivation.hypothesis List.mem_cons_self⟩)
 obtain ⟨hf⟩ := hf
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem zeroAtState (raw out state : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw z))) :
 Nonempty (Derivation body Delta ((graph2 accumulated out raw z).iff (graph1 reverse out raw))) := by
 apply programCases reverseRun ![suc raw,state] _
 intro beta rho Theta terminal hrho hr
 rw [binaryVectorRename] at hr
 simp only [iffRename,graph2Rename,graph1Rename,zRelabel]
 have hp' := renameInto hp rho Theta hrho
 simp only [graph2Rename,zRelabel] at hp'
 simp only [sucRelabel] at hr
 exact zeroAt (raw.relabel rho) (out.relabel rho) (state.relabel rho) terminal hp' hr

theorem zeroCorrespondence : OriginalTypedArgumentObservationsReverseInternalAccumulatorTargets.ZeroCorrespondence := by
 intro body alpha raw out
 apply programCases InternalPairing.pairing ![raw,z] _
 intro beta rho Theta state hrho hp
 rw [binaryVectorRename] at hp
 simp only [iffRename,graph2Rename,graph1Rename,zRelabel]
 simp only [zRelabel] at hp
 exact zeroAtState (raw.relabel rho) (out.relabel rho) state hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorZeroProof
