module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof
open OriginalTypedArgumentObservations
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stateRemaining (state raw acc parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc))) :
 Nonempty (Derivation body Delta (graph2 remaining raw state parameter)) :=
 unaryValue InternalUnpair.left (.projection 0) raw state ![state,parameter]
   (pairLeft state raw acc hp) (projectionValue 0 ![state,parameter])

theorem stateAccumulated (state raw acc parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc))) :
 Nonempty (Derivation body Delta (graph2 accumulated acc state parameter)) :=
 unaryValue InternalUnpair.right (.projection 0) acc state ![state,parameter]
   (pairRight state raw acc hp) (projectionValue 0 ![state,parameter])

theorem stepNil (R : Program 2) (state raw acc parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hn : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0))) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) state state parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![state,parameter]
 have hr := stateRemaining state raw acc parameter hp
 have ht := nilTag remaining raw xs hr hn
 exact sameNoIntro (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
   (advance R) (.projection 0) state (numeral 6) (numeral 7) xs
   ht (constantValue 7 xs) (numeralNe 6 7 (by decide)) (projectionValue 0 xs)

theorem stepCons (R : Program 2)
 (state raw acc parameter typ child tail packed observed typedObserved nextAcc nextState : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state raw acc)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 R observed packed parameter)))
 (hto : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObserved typ observed)))
 (hacc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc typedObserved acc)))
 (hnext : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing nextState tail nextAcc))) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) nextState state parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![state,parameter]
 have hr := stateRemaining state raw acc parameter hp
 have ht := consType remaining raw typ child tail xs hr hc
 have hchild := consHead remaining raw typ child tail xs hr hc
 have htail := consTail remaining raw typ child tail xs hr hc
 have hpk := binaryValue InternalPairing.pairing childType childRaw packed typ child xs hpacked ht hchild
 have hobs := binaryValue R childPacked (.projection 1) observed packed parameter xs ho hpk (projectionValue 1 xs)
 have htyped := binaryValue InternalPairing.pairing childType (childObservation R)
   typedObserved typ observed xs hto ht hobs
 have hlist := binaryValue InternalListCodec.consCode (typedObservation R) accumulated
   nextAcc typedObserved acc xs hacc htyped (stateAccumulated state raw acc parameter hp)
 have hv := binaryValue InternalPairing.pairing tailRaw (consOf (typedObservation R) accumulated)
   nextState tail nextAcc xs hnext htail hlist
 exact sameYesIntro (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7)
   (advance R) (.projection 0) nextState (numeral 7) (numeral 7) xs
   (consTag remaining raw typ child tail xs hr hc) (constantValue 7 xs) (by simpa only [InternalControlGraphSupportProof.equalEqn] using
     (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Delta) (numeral 7)))) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
