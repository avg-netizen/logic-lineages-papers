module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTerminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
open InternalRecursionClosureLogicProof (closedApply)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport (succOf constant)
open OriginalTypedArgumentObservations (reverseRun reverse reverseStep)
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem initialValue (raw acc state : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc))) :
 Nonempty (Derivation body Delta (graph2 initial state raw acc)) :=
 binaryValue InternalPairing.pairing (.projection 0) (.projection 1) state raw acc ![raw,acc]
   hp (projectionValue 0 ![raw,acc]) (projectionValue 1 ![raw,acc])

theorem fuelValue (raw acc : OTerm alpha) :
 Nonempty (Derivation body Delta (graph2 (succOf (.projection 0)) (suc raw) raw acc)) :=
 unaryValue .succ (.projection 0) (suc raw) raw ![raw,acc]
   (successorValue ![raw]) (projectionValue 0 ![raw,acc])

theorem runValue (raw acc state terminal : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state))) :
 Nonempty (Derivation body Delta (graph2 run terminal raw acc)) :=
 binaryValue reverseRun (succOf (.projection 0)) initial terminal (suc raw) state ![raw,acc]
   hr (fuelValue raw acc) (initialValue raw acc state hp)

theorem value (raw acc state terminal result : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state)))
 (hv : Nonempty (Derivation body Delta (graph1 InternalUnpair.right result terminal))) :
 Nonempty (Derivation body Delta (graph2 accumulated result raw acc)) :=
 unaryValue InternalUnpair.right run result terminal ![raw,acc] hv (runValue raw acc state terminal hp hr)

theorem recoverRight (raw acc state terminal result : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result raw acc))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right result terminal)) :=
 unaryRecover InternalUnpair.right run result terminal ![raw,acc] hv (runValue raw acc state terminal hp hr)

theorem terminalPair (raw acc state terminal result : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun terminal (suc raw) state)))
 (hv : Nonempty (Derivation body Delta (graph2 accumulated result raw acc))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing terminal z result)) := by
 have hz := closedApply
   (OriginalTypedArgumentObservationsReverseInternalTerminationProof.actualTermination body alpha raw state acc terminal)
   (andIntro hp hr)
 exact closedApply (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body alpha terminal z result)
   (andIntro hz (recoverRight raw acc state terminal result hp hr hv))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorGraphProof
