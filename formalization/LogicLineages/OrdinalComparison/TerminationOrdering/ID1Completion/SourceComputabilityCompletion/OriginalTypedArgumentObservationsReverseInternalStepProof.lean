module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalNumericIterationSupportProof InternalNumericIterationFusionProof
open OriginalTypedArgumentObservations
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepZero (state acc : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z acc))) :
 Nonempty (Derivation body Delta (graph1 reverseStep state state)) :=
 InternalAcceptanceBranchProof.zeroBranchIntro reverseRemaining (.projection 0) reverseAdvance
 state ![state] (pairLeft state z acc hp) (projectionValue 0 ![state])

theorem stepCons (state raw acc head tail nextAcc next : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc head acc)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing next tail nextAcc))) :
 Nonempty (Derivation body Delta (graph1 reverseStep next state)) := by
 let xs : Fin 1 → OTerm alpha := ![state]
 have hr := pairLeft state raw acc hp
 have hf := InternalListCodecSupportProof.consDestruction raw head tail hc
 have hh := unaryValue InternalListCodec.headCode reverseRemaining head raw xs (andLeft hf) hr
 have ht := unaryValue InternalListCodec.tailCode reverseRemaining tail raw xs (andLeft (andRight hf)) hr
 have hacc := pairRight state raw acc hp
 have hnew := binaryValue InternalListCodec.consCode
   (.composition InternalListCodec.headCode (fun _ : Fin 1 => reverseRemaining)) reverseAccumulated
   nextAcc head acc xs ha hh hacc
 have hv := binaryValue InternalPairing.pairing
   (.composition InternalListCodec.tailCode (fun _ : Fin 1 => reverseRemaining))
   (consOf (.composition InternalListCodec.headCode (fun _ : Fin 1 => reverseRemaining)) reverseAccumulated)
   next tail nextAcc xs hn ht hnew
 exact OriginalTypedDecoderInternalBranchProof.nonzeroAtIntro reverseRemaining (.projection 0) reverseAdvance
   next raw xs hr (OriginalTypedDecoderInternalListProof.consNonzero raw head tail hc) hv

theorem stopped (count state acc : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state z acc))) :
 Nonempty (Derivation body Delta (graph2 reverseRun state count state)) :=
 InternalNumericIterationFixedPointProof.fixedValue reverseStep count state (stepZero state acc hp)

theorem afterFirst (count state next out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph1 reverseStep next state)))
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun out count next))) :
 Nonempty (Derivation body Delta (graph2 reverseRun out (suc count) state)) := by
 have hone := repeatSuccValue reverseStep z state next state (repeatZeroValue reverseStep state) hf
 have hs := fusionValue reverseStep (suc z) count state next out hone hr
 have he : Derivation body Delta (eqn (add (suc z) count) (suc count)) :=
   trans (leftSuccessor z count) (congSuc (leftZero count))
 exact headTransport reverseRun out (add (suc z) count) (suc count) ![state] ⟨he⟩ hs

theorem padding (count spare initial out acc : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph2 reverseRun out count initial)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z acc))) :
 Nonempty (Derivation body Delta (graph2 reverseRun out (add count spare) initial)) :=
 fusionValue reverseStep count spare initial out out hr (stopped spare out acc hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalStepProof
