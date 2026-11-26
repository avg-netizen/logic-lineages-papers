module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The SAME typed R value is used in both transitions. All supplied values
are actual original graphs; the final row will query them internally. -/
theorem consSuffix (R : Program 2)
 (state1 state2 raw acc1 acc2 suffix parameter typ child tail packed observed typedObserved
 nextAcc1 nextAcc2 nextState1 nextState2 : OTerm alpha)
 (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state1 raw acc1)))
 (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing state2 raw acc2)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 R observed packed parameter)))
 (hto : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObserved typ observed)))
 (hacc1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc1 typedObserved acc1)))
 (hacc2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nextAcc2 typedObserved acc2)))
 (hnext1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing nextState1 tail nextAcc1)))
 (hnext2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing nextState2 tail nextAcc2))) :
 Nonempty (Derivation body Delta
  (graph2 (walkStep R) nextState1 state1 parameter ⊓
   (graph2 (walkStep R) nextState2 state2 parameter ⊓
    graph2 InternalApplicationValidityStackAppend.append nextAcc2 nextAcc1 suffix))) := by
 obtain ⟨h1⟩ := OriginalTypedArgumentObservationsInternalStepProof.stepCons R
   state1 raw acc1 parameter typ child tail packed observed typedObserved nextAcc1 nextState1
   hp1 hc hpacked ho hto hacc1 hnext1
 obtain ⟨h2⟩ := OriginalTypedArgumentObservationsInternalStepProof.stepCons R
   state2 raw acc2 parameter typ child tail packed observed typedObserved nextAcc2 nextState2
   hp2 hc hpacked ho hto hacc2 hnext2
 obtain ⟨happ⟩ := InternalApplicationValidityStackAppendListProof.consBackward
   nextAcc1 typedObserved acc1 suffix acc2 nextAcc2 hacc1 ha hacc2
 exact ⟨Derivation.conjunctionIntroduction h1 (Derivation.conjunctionIntroduction h2 happ)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsProof
