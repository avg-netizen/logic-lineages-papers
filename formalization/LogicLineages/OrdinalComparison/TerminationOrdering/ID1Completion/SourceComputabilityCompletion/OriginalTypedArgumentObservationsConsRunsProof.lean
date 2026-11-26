module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkedValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsConsRunsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walkStep

/-- Concrete raw-cons assembly from actual run/state graphs. All fuel and
accumulator equalities are supplied by the internally proved generic laws,
not by native evaluation. The outer CPS caller queries these state witnesses. -/
theorem fromRuns (R : Program 2)
 (raw typ child tail parameter packed observed typedObserved singleton
 initialParent initialTail initialSingleton outParent outTailOwn outTailLong
 parentRemaining tailRemaining combined tailReversed : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 R observed packed parameter)))
 (hto : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObserved typ observed)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton typedObserved z)))
 (hip : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initialParent raw z)))
 (hit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initialTail tail z)))
 (his : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initialSingleton tail singleton)))
 (hrp : Nonempty (Derivation body Delta (graph3 (walk R) outParent (suc raw) initialParent parameter)))
 (hrt : Nonempty (Derivation body Delta (graph3 (walk R) outTailOwn (suc tail) initialTail parameter)))
 (hrl : Nonempty (Derivation body Delta (graph3 (walk R) outTailLong raw initialTail parameter)))
 (hpp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing outParent parentRemaining combined)))
 (hpt : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing outTailOwn tailRemaining tailReversed))) :
 Nonempty (Derivation body Delta
   (graph2 InternalApplicationValidityStackAppend.append combined tailReversed singleton ⊓
    (graph2 (reversedObservations R) combined raw parameter ⊓
     graph2 (reversedObservations R) tailReversed tail parameter))) := by
 have hstep := OriginalTypedArgumentObservationsInternalStepProof.stepCons R
   initialParent raw z parameter typ child tail packed observed typedObserved singleton initialSingleton
   hip hc hpacked ho hto hs his
 have hresidual := walkAfterFirstRecover R raw initialParent initialSingleton outParent parameter hstep hrp
 have hbound := OriginalTypedArgumentObservationsInternalBoundProof.rawTailBound raw typ child tail hc
 have hownBound : Nonempty (Derivation body Delta (InternalLessThan.strictLess tail (suc tail))) :=
   InternalCoprimeMultipleBoundedProof.selfLtSucc tail
 have he := OriginalTypedArgumentObservationsFuelEqualityProof.sufficientCountsUnique R
   (suc tail) raw tail z initialTail parameter outTailOwn outTailLong hit hownBound hbound hrt hrl
 have hpt' := outputTransport InternalPairing.pairing outTailOwn outTailLong
   (Fin.cons tailRemaining (Fin.cons tailReversed Fin.elim0)) he hpt
 have hacc := OriginalTypedArgumentObservationsAccumulatorProof.accumulatorSuffix R body alpha Delta
   raw tail z singleton singleton initialTail initialSingleton parameter outTailLong outParent
   tailRemaining parentRemaining tailReversed combined hit his
   (InternalApplicationValidityStackAppendListProof.appendZeroValue singleton) hrl hresidual hpt' hpp
 obtain ⟨hacc⟩ := hacc
 obtain ⟨hp⟩ := OriginalTypedArgumentObservationsWalkedValueProof.reversedValue R
   initialParent raw parameter outParent parentRemaining combined hip hrp hpp
 obtain ⟨ht⟩ := OriginalTypedArgumentObservationsWalkedValueProof.reversedValue R
   initialTail tail parameter outTailOwn tailRemaining tailReversed hit hrt hpt
 exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight hacc)
   (Derivation.conjunctionIntroduction hp ht)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsConsRunsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsConsRunsProof
