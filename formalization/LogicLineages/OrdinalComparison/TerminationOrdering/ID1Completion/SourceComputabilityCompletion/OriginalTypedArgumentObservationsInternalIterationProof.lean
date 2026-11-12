module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsInternalStepProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameNoIntro)
open OriginalUniverseDecoderInternalFuelNumericSupportProof
open OriginalUniverseDecoderInternalFuelNumericFixedProof
open OriginalUniverseDecoderInternalFuelNumericFusionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every non-tag7 state is genuinely fixed, including nil and malformed
spines. This fixes behavior; it does not assert validity of the prefix. -/
theorem stoppedStep (R : Program 2) (state raw acc parameter tag : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
 (hn : Nonempty (Derivation body Delta (equal tag (numeral 7)).not)) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) state state parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![state,parameter]
 have htag := unaryValue InternalUnpair.left remaining tag raw xs ht (stateRemaining state raw acc parameter hp)
 exact sameNoIntro (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
   (advance R) (.projection 0) state tag (numeral 7) xs htag (constantValue 7 xs) hn (projectionValue 0 xs)

theorem stoppedIteration (R : Program 2) (count state raw acc parameter tag : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tag raw)))
 (hn : Nonempty (Derivation body Delta (equal tag (numeral 7)).not)) :
 Nonempty (Derivation body Delta (graph3 (walk R) state count state parameter)) :=
 fixedValue (walkStep R) count state parameter (stoppedStep R state raw acc parameter tag hp ht hn)

theorem walkAfterFirst (R : Program 2) (count state next out parameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 (walkStep R) next state parameter)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out count next parameter))) :
 Nonempty (Derivation body Delta (graph3 (walk R) out (suc count) state parameter)) := by
 have hone := repeatSuccValue (walkStep R) z state next state parameter (repeatZeroValue (walkStep R) state parameter) hf
 have hsum := fusionValue (walkStep R) (suc z) count state next out parameter hone hr
 have he : Derivation body Delta (eqn (add (suc z) count) (suc count)) :=
   InternalTagArithmeticSupportProof.trans (leftSuccessor z count) (congSuc (leftZero count))
 exact headTransport (walk R) out (add (suc z) count) (suc count) ![state,parameter] ⟨he⟩ hsum

theorem walkAfterFirstRecover (R : Program 2) (count state next out parameter : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 (walkStep R) next state parameter)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out (suc count) state parameter))) :
 Nonempty (Derivation body Delta (graph3 (walk R) out count next parameter)) := by
 have hone := repeatSuccValue (walkStep R) z state next state parameter (repeatZeroValue (walkStep R) state parameter) hf
 have he : Derivation body Delta (eqn (add (suc z) count) (suc count)) :=
   InternalTagArithmeticSupportProof.trans (leftSuccessor z count) (congSuc (leftZero count))
 have hsum := headTransport (walk R) out (suc count) (add (suc z) count) ![state,parameter]
   ⟨InternalTagArithmeticSupportProof.symm he⟩ hr
 exact fusionRecover (walkStep R) (suc z) count state next out parameter hone hsum

theorem walkPadding (R : Program 2) (count spare initial out parameter : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out count initial parameter)))
 (hf : Nonempty (Derivation body Delta (graph2 (walkStep R) out out parameter))) :
 Nonempty (Derivation body Delta (graph3 (walk R) out (add count spare) initial parameter)) :=
 fusionValue (walkStep R) count spare initial out out parameter hr (fixedValue (walkStep R) spare out parameter hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalIterationProof
